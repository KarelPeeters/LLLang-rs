use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, ExpressionInfo, Function, Global, GlobalSlot, Immediate, Instruction, InstructionInfo, Parameter, ParameterInfo, Program, Scoped, StackSlot, Terminator, Type, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::lattice::Lattice;
use crate::util::zip_eq;

/// Optimize load/store instructions:
/// * replace loads with previously stored values
/// * remove dead stores
#[derive(Debug)]
pub struct MemForwardingPass;

impl ProgramPass for MemForwardingPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let use_info = ctx.use_info(prog);
        let changed = mem_forwarding(prog, &use_info);

        PassResult {
            changed,
            preserved_dom_info: true,
            preserved_use_info: !changed,
        }
    }

    fn is_idempotent(&self) -> bool {
        true
    }
}

// TODO consider loads and stores with void type as dead?
fn mem_forwarding(prog: &mut Program, use_info: &UseInfo) -> bool {
    let mut loads_replaced = 0;
    let mut stores_removed = 0;

    // collect loads to replace
    let mut replacements = vec![];
    for func in use_info.funcs() {
        // reset cache per function
        let mut state = State {
            cache: Default::default(),
            undo: vec![],
            prog,
            use_info: &use_info,
            func,
        };

        for &block in use_info.func_blocks(func) {
            let instrs = state.prog.get_block(block).instructions.clone();

            for (index, &instr) in instrs.iter().enumerate() {
                let instr_info = state.prog.get_instr(instr);
                if let &InstructionInfo::Load { addr, ty: load_ty } = instr_info {
                    let loc = Location { ptr: addr, ty: load_ty };

                    let lattice = state.find_value_for_loc_at(loc, block, Some(index));

                    if let Some(value) = lattice.as_value_of_type(state.prog, load_ty) {
                        replacements.push((instr, value));
                    }
                }
            }
        }
    }

    // actually do replacements
    // (after collecting them to ensure we don't cause bugs by modifying the program in-place)
    for (instr, value) in replacements {
        let users_replaced = use_info.replace_value_usages(prog, instr.into(), value);
        if users_replaced > 0 {
            loads_replaced += 1;
        }
    }

    // remove dead stores
    // (in a separate pass because this can invalidate use_info)
    let mut liveness_cache = LivenessCache::default();
    for func in use_info.funcs() {
        for &block in use_info.func_blocks(func) {
            // TODO abstract this index/remove/increment mess somewhere
            //  it's like retain except we don't have ownership
            let mut instr_index = 0;

            loop {
                let block_info = prog.get_block(block);
                if instr_index >= block_info.instructions.len() {
                    break;
                }

                let instr = block_info.instructions[instr_index];
                let remove = if let &InstructionInfo::Store { addr, ty, value: _ } = prog.get_instr(instr) {
                    let loc = Location { ptr: addr, ty };
                    let liveness = compute_liveness(prog, func, block, instr_index + 1, loc, &mut liveness_cache);
                    match liveness {
                        Liveness::Dead => true,
                        Liveness::MaybeLive => false,
                    }
                } else {
                    false
                };

                if remove {
                    prog.get_block_mut(block).instructions.remove(instr_index);
                    stores_removed += 1;
                    // don't increment index
                } else {
                    instr_index += 1;
                }
            }
        }
    }

    println!("mem_forwarding replaced {} loads and removed {} stores", loads_replaced, stores_removed);
    loads_replaced > 0 || stores_removed > 0
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
struct Location {
    ptr: Value,
    ty: Type,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum PtrAlias {
    /// At least one of the pointers is undefined.
    Undef,
    /// Both pointers refer to exactly the same address.
    Exactly,
    /// We don't know whether the pointers alias.
    Unknown,
    /// Both pointers always refer to different addresses.
    No,
    /// If loads and stores only use the given type, this is the same as [PtrAlias::No].
    /// Otherwise the same as [PtrAlias::Unknown].
    NoIfType(Type),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum LocAlias {
    /// At least one of the locations is undefined.
    Undef,
    /// The locations overlap exactly.
    Exactly,
    /// We don't know whether the locations overlap or they overlap partially.
    UnknownOrPartial,
    /// The locations don't overlap at all.
    No,
}

// TODO allow for multiple slots to be tracked?
#[derive(Debug)]
enum Origin {
    /// The pointer is undefined.
    Undef,

    // A stack slot from the current function.
    FuncSlot(Option<StackSlot>),
    // A global slot.
    GlobalSlot(Option<GlobalSlot>),

    // Some location external to the current function frame.
    FuncExternal,

    /// We don't have enough information.
    Unknown,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Liveness {
    Dead,
    MaybeLive,
}

impl Liveness {
    // TODO implement general "lattice" or "merge" trait with top(), bottom(), merge() => fold, ...
    fn merge(left: Liveness, right: Liveness) -> Liveness {
        match (left, right) {
            (Liveness::MaybeLive, _) | (_, Liveness::MaybeLive) => Liveness::MaybeLive,
            (Liveness::Dead, Liveness::Dead) => Liveness::Dead,
        }
    }
}

/// The liveness cache stores the liveness for each location at the start of the given block.
/// This can also include a temporary "dead" assumption to break loops.
type LivenessCache = HashMap<(Block, Location), Liveness>;

fn compute_liveness(prog: &Program, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // the values in the cache apply to the start of the block
    if start == 0 {
        match cache.entry((block, loc)) {
            // we've found the answer in the cache already, great!
            Entry::Occupied(entry) => return *entry.get(),
            // otherwise temporarily assume the current block is dead
            Entry::Vacant(entry) => entry.insert(Liveness::Dead),
        };
    }

    // check the rest of the block and its successors
    let liveness = compute_liveness_inner(prog, func, block, start, loc, cache);

    // put the true liveness into the cache
    if start == 0 {
        let prev = cache.insert((block, loc), liveness);
        assert_eq!(prev, Some(Liveness::Dead));
    }

    liveness
}

/// The same as [compute_liveness] except we don't manage the cache here.
fn compute_liveness_inner(prog: &Program, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // check the following instructions
    if let Some(liveness) = compute_liveness_by_instructions(prog, func, block, start, loc) {
        return liveness;
    }

    // fallthrough to the successors
    match &prog.get_block(block).terminator {
        Terminator::Jump { target } => {
            compute_liveness(prog, func, target.block, 0, loc, cache)
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            Liveness::merge(
                compute_liveness(prog, func, true_target.block, 0, loc, cache),
                compute_liveness(prog, func, false_target.block, 0, loc, cache),
            )
        }
        Terminator::Return { value: _ } => {
            let origin = pointer_origin(prog, func, loc.ptr);
            match origin {
                // function-internal, so cannot be observed after return
                Origin::FuncSlot(_) => Liveness::Dead,
                // maybe external, so can potentially be observed
                // TODO maybe we can do something better with undef here?
                Origin::Undef | Origin::GlobalSlot(_) | Origin::FuncExternal | Origin::Unknown => Liveness::MaybeLive,
            }
        }
        // no successor, so dead
        Terminator::Unreachable => Liveness::Dead,
        Terminator::LoopForever => Liveness::Dead,
    }
}

// TODO ideally this would use some common "instruction side effect" infrastructure
fn compute_liveness_by_instructions(prog: &Program, func: Function, block: Block, start: usize, loc: Location) -> Option<Liveness> {
    let block_info = prog.get_block(block);
    for &instr in &block_info.instructions[start..] {
        match *prog.get_instr(instr) {
            // (maybe) aliasing load => alive
            InstructionInfo::Load { addr, ty } => {
                let load_loc = Location { ptr: addr, ty };
                match locations_alias(prog, func, loc, load_loc) {
                    // could alias, we have to assume live
                    LocAlias::Exactly | LocAlias::UnknownOrPartial => return Some(Liveness::MaybeLive),
                    // can't alias, keep going
                    LocAlias::Undef | LocAlias::No => {}
                }
            }
            // (exactly) aliasing store => dead
            InstructionInfo::Store { addr, ty, value: _ } => {
                let store_loc = Location { ptr: addr, ty };
                match locations_alias(prog, func, loc, store_loc) {
                    // value is overwritten, we know the previous one is dead
                    // TODO a "covering" alias is enough already, it doesn't have to be exact
                    LocAlias::Exactly => return Some(Liveness::Dead),
                    // may not be overwritten, keep going
                    // TODO maybe we can do something better with undef here?
                    LocAlias::Undef | LocAlias::UnknownOrPartial | LocAlias::No => {}
                }
            }

            // these could have side effects, we have to assume live
            // TODO we can do better for calls
            InstructionInfo::Call { .. } => return Some(Liveness::MaybeLive),
            InstructionInfo::BlackBox { .. } => return Some(Liveness::MaybeLive),
        }
    }

    None
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
enum Side {
    Start,
    End,
}

impl Side {
    fn from_index(index: Option<usize>) -> Option<Side> {
        match index {
            None => Some(Side::End),
            Some(0) => Some(Side::Start),
            _ => None,
        }
    }
}

type Key = (Location, Block, Side);

struct State<'p, 'u> {
    cache: HashMap<Key, Lattice>,
    undo: Vec<Undo>,

    // util to avoid passing a bunch of params repeatedly
    prog: &'p mut Program,
    use_info: &'u UseInfo,
    func: Function,
}

// TODO general undo infrastructure? can we wrap the entire program in it or is that too slow/tricky?
#[derive(Debug)]
enum Undo {
    CacheInsert(Key),
    DefineParam(Parameter),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Marker(usize);

enum WalkResult {
    Lattice(Lattice),
    ReachedStart {
        matching_load: Option<Instruction>,
    },
}

impl<'p, 'u> State<'p, 'u> {
    fn mark(&self) -> Marker {
        Marker(self.undo.len())
    }

    fn rollback(&mut self, marker: Marker) {
        let marker = marker.0;
        for undo in self.undo.drain(marker..).rev() {
            match undo {
                Undo::CacheInsert(key) => {
                    let prev = self.cache.remove(&key);
                    assert!(prev.is_some());
                }
                Undo::DefineParam(param) => {
                    self.prog.nodes.params.pop(param);
                }
            }
        }
        assert_eq!(self.undo.len(), marker);
    }

    fn cache_get(&self, key: Key) -> Option<Lattice> {
        self.cache.get(&key).copied()
    }

    fn cache_insert(&mut self, key: Key, value: Lattice) {
        let prev = self.cache.insert(key, value);

        match prev {
            None => self.undo.push(Undo::CacheInsert(key)),
            Some(prev) => {
                assert!(prev == value, "prev should be None or Some({:?}), got {:?}", value, prev);
                // no need to undo, this insertion didn't change anything
            }
        }
    }

    fn define_param(&mut self, info: ParameterInfo) -> Parameter {
        let param = self.prog.define_param(info);
        self.undo.push(Undo::DefineParam(param));
        param
    }

    fn find_value_for_loc_at(&mut self, loc: Location, block: Block, index: Option<usize>) -> Lattice {
        // check cache
        if let Some(side) = Side::from_index(index) {
            if let Some(result) = self.cache_get((loc, block, side)) {
                return result;
            }
        }

        // evaluate the value
        let result = self.find_value_for_loc_at_inner(loc, block, index);

        // put into cache
        if let Some(side) = Side::from_index(index) {
            self.cache_insert((loc, block, side), result);
        }

        result
    }

    fn find_value_for_loc_at_inner(&mut self, loc: Location, block: Block, index: Option<usize>) -> Lattice {
        // look at the preceding instructions in this block
        let walk = self.walk_block_instructions_from(loc, block, index);
        let matching_load = match walk {
            WalkResult::Lattice(value) => return value,
            WalkResult::ReachedStart { matching_load } => matching_load,
        };

        // we've reached the start of the block, check the cache for it
        if let Some(value) = self.cache_get((loc, block, Side::Start)) {
            return value;
        }

        // if we've reached the func entry the value depends on the origin
        if self.use_info.block_only_used_as_func_entry(block) {
            return match pointer_origin(self.prog, self.func, loc.ptr) {
                Origin::Undef => Lattice::Undef,
                Origin::Unknown | Origin::GlobalSlot(_) | Origin::FuncExternal => Lattice::Overdef,
                Origin::FuncSlot(_) => Lattice::Undef,
            };
        }

        // if there are pred blocks, try inserting a block param
        if self.use_info.block_only_used_in_targets(block) {
            if let Some(value) = self.try_build_block_param(loc, block) {
                return value;
            }
        }

        // TODO we could try merging func entry and other pred values here
        //   alternatively just require there to be an empty entry block we can add the arg to?

        // if there was a matching load use it
        if let Some(load) = matching_load {
            return Lattice::Known(load.into());
        }

        // we don't know anything
        Lattice::Overdef
    }

    fn walk_block_instructions_from(&mut self, loc: Location, block: Block, index: Option<usize>) -> WalkResult {
        let block_info = self.prog.get_block(block);
        let index = index.unwrap_or(block_info.instructions.len());

        // keep track of the earliest load that aliases
        // (earliest to ensure that repeated loads all converge to the first one)
        let mut first_matching_load = None;
        let mut clobbered = false;

        // walk the instructions backwards
        for &instr in block_info.instructions[0..index].iter().rev() {
            match *self.prog.get_instr(instr) {
                // if the store aliases, return its value
                InstructionInfo::Store { addr: store_ptr, ty: store_ty, value } => {
                    let store_loc = Location { ptr: store_ptr, ty: store_ty };
                    match locations_alias(self.prog, self.func, loc, store_loc) {
                        // propagate undef
                        LocAlias::Undef => return WalkResult::Lattice(Lattice::Undef),
                        // we know the exact value last stored to loc!
                        LocAlias::Exactly => return WalkResult::Lattice(Lattice::Known(value)),
                        // we have to give up
                        LocAlias::UnknownOrPartial => {
                            clobbered = true;
                            break;
                        }
                        // continue walking backwards
                        LocAlias::No => {}
                    }
                }

                // if the load aliases, keep it around for potential reuse
                InstructionInfo::Load { addr: load_addr, ty: load_ty } => {
                    let load_loc = Location { ptr: load_addr, ty: load_ty };
                    match locations_alias(self.prog, self.func, loc, load_loc) {
                        // unclear, we could reuse if the type matches but is that useful?
                        LocAlias::Undef => {}
                        // we can't reuse the load
                        LocAlias::UnknownOrPartial | LocAlias::No => {}
                        // we can reuse it
                        LocAlias::Exactly => {
                            first_matching_load = Some(instr);
                        }
                    }
                }

                // could have side effects, we have to give up
                // TODO we can do better for calls:
                //   * side effect free functions
                //   * if we don't leak a slot, external or global slot to external code/memory/this call
                //        we can continue
                InstructionInfo::Call { .. } | InstructionInfo::BlackBox { .. } => {
                    clobbered = true;
                    break;
                }
            }
        }

        if clobbered {
            match first_matching_load {
                None => WalkResult::Lattice(Lattice::Overdef),
                Some(load) => WalkResult::Lattice(Lattice::Known(load.into())),
            }
        } else {
            WalkResult::ReachedStart { matching_load: first_matching_load }
        }
    }

    fn try_build_block_param(&mut self, loc: Location, block: Block) -> Option<Lattice> {
        let mark = self.mark();

        // define param and immediately put it in the cache to break cycles
        let param = self.define_param(ParameterInfo { ty: loc.ty });
        self.cache_insert((loc, block, Side::Start), Lattice::Known(param.into()));

        // map predecessors to values
        let preds = self.use_info[block].to_vec();
        let mut pred_args = vec![];

        for &pred in &preds {
            let pred = unwrap_match!(pred, BlockUsage::Target { pos, kind: _ } => pos.block);
            let lattice = self.find_value_for_loc_at(loc, pred, None);

            let value = match lattice.as_value_of_type(self.prog, loc.ty) {
                Some(value) => value,
                None => {
                    // failed to get value for predecessor: rollback and mark this block start as doomed
                    self.rollback(mark);
                    self.cache_insert((loc, block, Side::Start), Lattice::Overdef);
                    return None;
                }
            };

            pred_args.push(value);
        };

        // success!
        // push param and pred args
        self.prog.get_block_mut(block).params.push(param);
        for (pred, arg) in zip_eq(preds, pred_args) {
            let (pos, kind) = unwrap_match!(pred, BlockUsage::Target { pos, kind } => (pos, kind));
            let target = kind.get_target_mut(&mut self.prog.get_block_mut(pos.block).terminator);
            target.args.push(arg);
        }

        Some(Lattice::Known(param.into()))
    }
}

fn locations_alias(prog: &Program, func: Function, left: Location, right: Location) -> LocAlias {
    let same_ty = left.ty == right.ty;

    match pointers_alias(prog, func, left.ptr, right.ptr) {
        PtrAlias::Undef => LocAlias::Undef,
        PtrAlias::Unknown => LocAlias::UnknownOrPartial,
        PtrAlias::No => LocAlias::No,

        PtrAlias::Exactly => {
            if same_ty {
                LocAlias::Exactly
            } else {
                LocAlias::UnknownOrPartial
            }
        }
        PtrAlias::NoIfType(expected_ty) => {
            if same_ty && left.ty == expected_ty {
                LocAlias::No
            } else {
                LocAlias::UnknownOrPartial
            }
        }
    }
}

fn pointers_alias(prog: &Program, func: Function, ptr_left: Value, ptr_right: Value) -> PtrAlias {
    let simple_left = core_ptr(prog, ptr_left);
    let simple_right = core_ptr(prog, ptr_right);

    if simple_left.base.is_undef() || simple_right.base.is_undef() {
        return PtrAlias::Undef;
    }
    if simple_left == simple_right {
        return PtrAlias::Exactly;
    }

    if simple_left.base == simple_right.base {
        match (simple_left.offset, simple_right.offset) {
            (Offset::None, Offset::None) => unreachable!(),

            // zero offset compared to non-zero offset
            (Offset::None, Offset::Pointer(ty, index)) | (Offset::Pointer(ty, index), Offset::None) => {
                assert!(!prog.is_zero_sized_type(ty) && index != 0);
                return PtrAlias::NoIfType(ty);
            }

            (Offset::Pointer(left_ty, left_index), Offset::Pointer(right_ty, right_index)) => {
                if left_ty == right_ty {
                    return if left_index == right_index {
                        PtrAlias::Exactly
                    } else {
                        PtrAlias::NoIfType(left_ty)
                    };
                }
            }

            (Offset::TupleField(left_ty, left_index), Offset::TupleField(right_ty, right_index)) => {
                if left_ty == right_ty {
                    return if left_index == right_index {
                        PtrAlias::Exactly
                    } else {
                        PtrAlias::NoIfType(left_ty)
                    };
                };
            }

            _ => {}
        }

        // bases still match, so origin check won't achieve anything anyway
        return PtrAlias::Unknown;
    }

    let origin_left = pointer_origin(prog, func, simple_left.base);
    let origin_right = pointer_origin(prog, func, simple_right.base);
    if !origins_can_alias(origin_left, origin_right) {
        return PtrAlias::No;
    }

    PtrAlias::Unknown
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct CorePtr {
    base: Value,
    offset: Offset,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Offset {
    None,
    Pointer(Type, i64),
    TupleField(Type, u32),
}

fn core_ptr(prog: &Program, ptr: Value) -> CorePtr {
    assert_eq!(prog.type_of_value(ptr), prog.ty_ptr());

    if let Some(expr) = ptr.as_expr() {
        match *prog.get_expr(expr) {
            ExpressionInfo::PointerOffSet { ty, base, index } => {
                if prog.is_zero_sized_type(ty) {
                    return core_ptr(prog, base);
                }
                if let Some(index) = index.as_const() {
                    assert_eq!(prog.get_type(index.ty).unwrap_int(), Some(prog.ptr_size_bits()));
                    let index = index.value.signed();

                    return match index {
                        0 => core_ptr(prog, base),
                        _ => CorePtr { base, offset: Offset::Pointer(ty, index) }
                    };
                }
            }
            ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } => {
                // index == 0 is not enough to decay to base pointer, since the layout of tuples is decided by the backend
                // however, single-element tuples are still guaranteed to have the same layout as the single item inside them
                let field_count = prog.get_type(tuple_ty).unwrap_tuple().unwrap().fields.len();
                assert!(field_count > 0);
                if field_count == 1 {
                    return core_ptr(prog, base);
                }

                return CorePtr {
                    base,
                    offset: Offset::TupleField(tuple_ty, index),
                };
            }
            _ => panic!("Unexpected pointer-yielding expression {:?}", expr),
        }
    }

    CorePtr {
        base: ptr,
        offset: Offset::None,
    }
}

// TODO do some proper dataflow analysis here
//  specifically this would be useful for things like:
//    * phis
//    * load/store forwarding, which is what we're doing here in the first place!)
// TODO ideally incorporate this into SCCP?
fn pointer_origin(prog: &Program, func: Function, ptr: Value) -> Origin {
    assert_eq!(prog.type_of_value(ptr), prog.ty_ptr());

    match ptr {
        Value::Immediate(value) => match value {
            Immediate::Void => unreachable!("Void cannot have pointer type: {:?}", ptr),
            Immediate::Undef(_) => Origin::Undef,
            Immediate::Const(_) => Origin::FuncExternal,
        },
        Value::Global(value) => match value {
            Global::Func(_) => unreachable!("Function cannot have pointer type: {:?}", ptr),
            Global::Extern(_) => Origin::FuncExternal,
            Global::Data(_) => Origin::FuncExternal,
            Global::GlobalSlot(slot) => Origin::GlobalSlot(Some(slot)),
        },
        Value::Scoped(value) => match value {
            Scoped::Param(param) => {
                // check if this is a function param
                if prog.get_block(prog.get_func(func).entry).params.contains(&param) {
                    Origin::FuncExternal
                } else {
                    Origin::Unknown
                }
            }
            Scoped::Slot(slot) => Origin::FuncSlot(Some(slot)),
            Scoped::Instr(instr) => match prog.get_instr(instr) {
                InstructionInfo::Load { .. } => Origin::Unknown,
                InstructionInfo::Store { .. } =>
                    unreachable!("Instruction cannot return pointer type: {:?}", instr),
                InstructionInfo::Call { .. } => Origin::Unknown,
                InstructionInfo::BlackBox { .. } => Origin::Unknown,
            }
        },
        Value::Expr(expr) => match prog.get_expr(expr) {
            ExpressionInfo::Arithmetic { .. } | ExpressionInfo::Comparison { .. } =>
                unreachable!("Expression cannot return pointer type: {:?}", expr),
            &ExpressionInfo::TupleFieldPtr { base, index: _, tuple_ty: _, } => pointer_origin(prog, func, base),
            &ExpressionInfo::PointerOffSet { ty: _, base, index: _ } => pointer_origin(prog, func, base),
            // TODO when we add ptr/int casts maybe we can look through them?
            ExpressionInfo::Cast { .. } => Origin::Unknown,
        }
    }
}

fn origins_can_alias(left: Origin, right: Origin) -> bool {
    match (left, right) {
        (Origin::Undef, _) | (_, Origin::Undef) => false,

        (Origin::Unknown, _) | (_, Origin::Unknown) => true,
        (Origin::FuncExternal, Origin::FuncExternal) => true,

        (Origin::FuncSlot(left), Origin::FuncSlot(right)) => match (left, right) {
            (None, _) | (_, None) => true,
            (Some(left), Some(right)) => left == right,
        },
        (Origin::GlobalSlot(left), Origin::GlobalSlot(right)) => match (left, right) {
            (None, _) | (_, None) => true,
            (Some(left), Some(right)) => left == right,
        },

        (Origin::FuncExternal | Origin::GlobalSlot(_), Origin::FuncSlot(_)) => false,
        (Origin::FuncSlot(_), Origin::FuncExternal | Origin::GlobalSlot(_)) => false,

        (Origin::FuncExternal, Origin::GlobalSlot(_)) => true,
        (Origin::GlobalSlot(_), Origin::FuncExternal) => true,
    }
}
