use std::collections::HashMap;
use std::collections::hash_map::Entry;
use crate::mid::analyse::alias;
use crate::mid::analyse::alias::{LocAlias, Location, Origin};

use crate::mid::analyse::usage::{BlockUsage, TargetKind};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Parameter, ParameterInfo, Program, Terminator, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::mid::util::lattice::Lattice;
use crate::util::zip_eq;

// TODO allow potentially aliasing store to still propagate the value if the value stores is the same as the existing one
//  eg. https://trust-in-soft.com/blog/2020/04/06/gcc-always-assumes-aligned-pointer-accesses/
//  but tricky, since now we also need to keep track of values, not just pointers

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
            use_info,
            func,
        };

        for &block in use_info.func_blocks(func) {
            let instrs = state.prog.get_block(block).instructions.clone();

            for (index, &instr) in instrs.iter().enumerate() {
                // no point trying to replace unused loads
                if use_info[instr].is_empty() {
                    continue;
                }

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
                    let liveness = compute_liveness(prog, use_info, func, block, instr_index + 1, loc, &mut liveness_cache);
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

fn compute_liveness(prog: &Program, use_info: &UseInfo, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
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
    let liveness = compute_liveness_inner(prog, use_info, func, block, start, loc, cache);

    // put the true liveness into the cache
    if start == 0 {
        let prev = cache.insert((block, loc), liveness);
        assert_eq!(prev, Some(Liveness::Dead));
    }

    liveness
}

/// The same as [compute_liveness] except we don't manage the cache here.
fn compute_liveness_inner(prog: &Program, use_info: &UseInfo, func: Function, block: Block, start: usize, loc: Location, cache: &mut LivenessCache) -> Liveness {
    // check the following instructions
    if let Some(liveness) = compute_liveness_by_instructions(prog, use_info, func, block, start, loc) {
        return liveness;
    }

    // fallthrough to the successors
    match &prog.get_block(block).terminator {
        Terminator::Jump { target } => {
            compute_liveness(prog, use_info, func, target.block, 0, loc, cache)
        }
        Terminator::Branch { cond: _, true_target, false_target } => {
            Liveness::merge(
                compute_liveness(prog, use_info, func, true_target.block, 0, loc, cache),
                compute_liveness(prog, use_info, func, false_target.block, 0, loc, cache),
            )
        }
        Terminator::Return { value: _ } => {
            let origin = alias::pointer_origin(prog, func, loc.ptr);
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
fn compute_liveness_by_instructions(prog: &Program, use_info: &UseInfo, func: Function, block: Block, start: usize, loc: Location) -> Option<Liveness> {
    let block_info = prog.get_block(block);
    for &instr in &block_info.instructions[start..] {
        match *prog.get_instr(instr) {
            // (maybe) aliasing load => alive
            InstructionInfo::Load { addr, ty } => {
                let load_loc = Location { ptr: addr, ty };
                match alias::locations_alias(prog, use_info, func, loc, load_loc) {
                    // could alias, we have to assume live
                    LocAlias::Exactly | LocAlias::UnknownOrPartial => return Some(Liveness::MaybeLive),
                    // can't alias, keep going
                    LocAlias::Undef | LocAlias::No => {}
                }
            }
            // (exactly) aliasing store => dead
            InstructionInfo::Store { addr, ty, value: _ } => {
                let store_loc = Location { ptr: addr, ty };
                match alias::locations_alias(prog, use_info, func, loc, store_loc) {
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
            InstructionInfo::BlackHole { .. } => return Some(Liveness::MaybeLive),
            InstructionInfo::MemBarrier { .. } => return Some(Liveness::MaybeLive),
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
    PushBlockParam(Block, usize, Parameter),
    PushTargetArg(Block, TargetKind, usize, Value),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct Marker(usize);

#[derive(Debug)]
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
                Undo::PushBlockParam(block, index, param) => {
                    let block = self.prog.get_block_mut(block);
                    assert_eq!(block.params.len(), index + 1);
                    assert_eq!(block.params.pop(), Some(param));
                }
                Undo::PushTargetArg(block, kind, index, arg) => {
                    let block = self.prog.get_block_mut(block);
                    let target = kind.get_target_mut(&mut block.terminator);
                    assert_eq!(target.args.len(), index + 1);
                    assert_eq!(target.args.pop(), Some(arg));
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

    fn push_block_param(&mut self, block: Block, param: Parameter) {
        let params = &mut self.prog.get_block_mut(block).params;

        let index = params.len();
        params.push(param);
        self.undo.push(Undo::PushBlockParam(block, index, param));
    }

    fn push_target_arg(&mut self, block: Block, kind: TargetKind, arg: Value) {
        let term = &mut self.prog.get_block_mut(block).terminator;
        let target = kind.get_target_mut(term);
        let args = &mut target.args;

        let index = args.len();
        args.push(arg);
        self.undo.push(Undo::PushTargetArg(block, kind, index, arg));
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
        if let Some(start_value) = self.cache_get((loc, block, Side::Start)) {
            // if we got a useless start value use the matching load instead
            if let Lattice::Overdef = start_value {
                if let Some(matching_load) = matching_load {
                    return Lattice::Known(matching_load.into());
                }
            }

            return start_value;
        }

        // if we've reached the func entry the value depends on the origin
        if self.use_info.block_only_used_as_func_entry(block) {
            match alias::pointer_origin(self.prog, self.func, loc.ptr) {
                Origin::Undef => return Lattice::Undef,
                Origin::FuncSlot(_) => return Lattice::Undef,
                Origin::Unknown | Origin::GlobalSlot(_) | Origin::FuncExternal => {
                    // fallthrough, we might still have a matching load
                }
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
        let use_info = self.use_info;
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
                    match alias::locations_alias(self.prog, use_info, self.func, loc, store_loc) {
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
                    match alias::locations_alias(self.prog, use_info, self.func, loc, load_loc) {
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

                // TODO have some general side-effect property checker for functions
                InstructionInfo::Call { .. } => {
                    let origin = alias::pointer_origin(self.prog, self.func, loc.ptr);
                    let call_could_interact = match origin {
                        Origin::FuncSlot(Some(slot)) =>
                            !use_info.value_only_used_as_load_store_addr(self.prog, slot.into(), None, |_| true),
                        Origin::GlobalSlot(Some(slot)) =>
                            !use_info.value_only_used_as_load_store_addr(self.prog, slot.into(), None, |_| true),

                        Origin::Undef => false,
                        Origin::GlobalSlot(None) | Origin::FuncSlot(None) => true,
                        Origin::FuncExternal | Origin::Unknown => true,
                    };

                    if call_could_interact {
                        clobbered = true;
                        break;
                    }
                }
                InstructionInfo::MemBarrier | InstructionInfo::BlackHole { .. } => {
                    // TODO we pretend we also write to non-leaked pointers, maybe that's too strong?
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

        // (tentative) success!
        // push param and pred args
        self.push_block_param(block, param);
        for (pred, arg) in zip_eq(preds, pred_args) {
            let (pos, kind) = unwrap_match!(pred, BlockUsage::Target { pos, kind } => (pos, kind));
            self.push_target_arg(pos.block, kind, arg);
        }

        Some(Lattice::Known(param.into()))
    }
}
