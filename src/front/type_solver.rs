use std::collections::VecDeque;

use itertools::Itertools;

use crate::front::ast;
use crate::front::cst::{IntTypeInfo, Type, TypeInfo, TypeStore};
use crate::mid::ir::Signed;
use crate::util::{IndexMutTwice, zip_eq};

type VarTypeInfo<'ast> = TypeInfo<'ast, TypeVar>;

/// Represents the type of an expression in the program.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct TypeVar(usize);

#[derive(Debug)]
struct VarState<'ast> {
    // these never change after initial creation
    origin: Origin<'ast>,
    post_check: PostCheck,

    // these change during solving
    default_void: bool,
    info: Option<VarTypeInfo<'ast>>,
}

#[derive(Debug, Copy, Clone)]
enum PostCheck {
    None,
    Int(Option<Signed>),
    BoolOrInt(Option<Signed>),
}

#[derive(Copy, Clone)]
pub enum Origin<'ast> {
    FullyKnown,
    Expression(&'ast ast::Expression),
    Declaration(&'ast ast::Declaration),
    ForIndex(&'ast ast::ForStatement),
}

impl std::fmt::Debug for Origin<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Origin::FullyKnown => write!(f, "Origin::FullyKnown"),
            Origin::Expression(a) => write!(f, "Origin::Expression({:?})", a.span),
            Origin::Declaration(a) => write!(f, "Origin::Declaration({:?})", a.span),
            Origin::ForIndex(a) => write!(f, "Origin::ForIndex({:?})", a.span),
        }
    }
}

//TODO don't assert anywhere, return an error instead. look at unwrap, expect, panic, ...
//TODO print out an instance once, to see how much duplicate noise there is
pub struct TypeProblem<'ast> {
    state: Vec<VarState<'ast>>,

    //constraints
    matches: VecDeque<(TypeVar, TypeVar)>,
    index_constraints: VecDeque<IndexConstraint<'ast>>,
    add_sub_constraints: VecDeque<AddSubConstraint>,

    //basic types
    ty_void: TypeVar,
    ty_bool: TypeVar,

    ty_u8: TypeVar,
    ty_isize: TypeVar,
    ty_usize: TypeVar,
}

pub struct TypeSolution {
    state: Vec<Type>,
}

struct AddSubConstraint {
    left: TypeVar,
    right: TypeVar,
}

#[derive(Debug, Copy, Clone)]
struct IndexConstraint<'ast> {
    target: TypeVar,
    result: TypeVar,
    index: IndexKind<'ast>,
}

#[derive(Debug, Copy, Clone)]
enum IndexKind<'ast> {
    Tuple(u32),
    Array,
    Struct(&'ast str),
}

impl IndexKind<'_> {
    fn name(self) -> &'static str {
        match self {
            IndexKind::Tuple(_) => "tuple",
            IndexKind::Array => "array",
            IndexKind::Struct(_) => "struct",
        }
    }
}

impl<'ast> TypeProblem<'ast> {
    pub fn new(ptr_size_bits: u32) -> Self {
        let mut problem = TypeProblem {
            state: vec![],
            matches: Default::default(),
            index_constraints: Default::default(),
            add_sub_constraints: Default::default(),

            ty_void: TypeVar(usize::MAX),
            ty_bool: TypeVar(usize::MAX),
            ty_u8: TypeVar(usize::MAX),
            ty_isize: TypeVar(usize::MAX),
            ty_usize: TypeVar(usize::MAX),
        };

        problem.ty_void = problem.known(Origin::FullyKnown, TypeInfo::Void);
        problem.ty_bool = problem.known(Origin::FullyKnown, TypeInfo::Bool);

        problem.ty_u8 = problem.known(Origin::FullyKnown, TypeInfo::Int(IntTypeInfo::U8));

        let isize_info = IntTypeInfo::new(Signed::Signed, ptr_size_bits);
        let usize_info = IntTypeInfo::new(Signed::Unsigned, ptr_size_bits);
        problem.ty_isize = problem.known(Origin::FullyKnown, TypeInfo::Int(isize_info));
        problem.ty_usize = problem.known(Origin::FullyKnown, TypeInfo::Int(usize_info));

        problem
    }

    /// The current amount of `TypeVar`s defined in this problem.
    pub fn len(&self) -> usize {
        self.state.len()
    }

    fn new_var(&mut self, origin: Origin<'ast>, info: Option<VarTypeInfo<'ast>>, post_check: PostCheck, default_void: bool) -> TypeVar {
        // Some(Wildcard) means that we don't know anything about a type, so convert it to None
        let info = info.filter(|info| info != &VarTypeInfo::Wildcard);

        let i = self.state.len();
        self.state.push(VarState { origin, post_check, default_void, info });
        TypeVar(i)
    }

    pub fn ty_void(&self) -> TypeVar {
        self.ty_void
    }

    pub fn ty_bool(&self) -> TypeVar {
        self.ty_bool
    }

    pub fn ty_u8(&self) -> TypeVar {
        self.ty_u8
    }

    pub fn ty_isize(&self) -> TypeVar {
        self.ty_isize
    }

    pub fn ty_usize(&self) -> TypeVar {
        self.ty_usize
    }

    /// Create a new TypeVar without any known type information.
    pub fn unknown(&mut self, origin: Origin<'ast>) -> TypeVar {
        self.new_var(origin, None, PostCheck::None, false)
    }

    /// Create a new TypeVar without a known type, but that gets assigned the void type if at the end of inference this
    /// type still has no inferred type.
    pub fn unknown_default_void(&mut self, origin: Origin<'ast>) -> TypeVar {
        self.new_var(origin, None, PostCheck::None, true)
    }

    /// Create a new TypeVar that can be assigned any integer type.
    pub fn unknown_int(&mut self, origin: Origin<'ast>, signed: Option<Signed>) -> TypeVar {
        self.new_var(origin, None, PostCheck::Int(signed), false)
    }

    /// Create a new TypeVar that can be assigned any integer type.
    pub fn unknown_int_or_bool(&mut self, origin: Origin<'ast>, signed: Option<Signed>) -> TypeVar {
        self.new_var(origin, None, PostCheck::BoolOrInt(signed), false)
    }

    /// Create a new TypeVar with a known type pattern
    pub fn known(&mut self, origin: Origin<'ast>, info: VarTypeInfo<'ast>) -> TypeVar {
        self.new_var(origin, Some(info), PostCheck::None, false)
    }

    /// Create a new TypeVar with a fully known type.
    pub fn fully_known(&mut self, types: &TypeStore<'ast>, ty: Type) -> TypeVar {
        let info = types[ty].map_ty(&mut |&child_ty| {
            self.fully_known(types, child_ty)
        });
        self.known(Origin::FullyKnown, info)
    }

    /// Create a new TypeVar representing the type of a tuple index expression.
    pub fn tuple_index(&mut self, origin: Origin<'ast>, target: TypeVar, index: u32) -> TypeVar {
        let result = self.unknown(origin);
        self.index_constraints.push_back(IndexConstraint { target, result, index: IndexKind::Tuple(index) });
        result
    }

    /// Create a new TypeVar representing the type of a struct index expression.
    pub fn struct_index(&mut self, origin: Origin<'ast>, target: TypeVar, index: &'ast str) -> TypeVar {
        let result = self.unknown(origin);
        self.index_constraints.push_back(IndexConstraint { target, result, index: IndexKind::Struct(index) });
        result
    }

    /// Create a new TypeVar representing the result type of an array index expression.
    pub fn array_index(&mut self, origin: Origin<'ast>, target: TypeVar) -> TypeVar {
        let result = self.unknown(origin);
        self.index_constraints.push_back(IndexConstraint { target, result, index: IndexKind::Array });
        result
    }

    /// Require that two types match
    pub fn equal(&mut self, left: TypeVar, right: TypeVar) {
        self.matches.push_back((left, right))
    }

    /// Require the following:
    /// * if `left` is an integer type `right` should be the same type
    /// * if `left` is a pointer type `right` should be the type Int
    pub fn add_sub_constraint(&mut self, left: TypeVar, right: TypeVar) {
        self.add_sub_constraints.push_back(AddSubConstraint { left, right });
    }
}

/// Solver implementation
impl<'ast> TypeProblem<'ast> {
    pub fn solve(mut self, types: &mut TypeStore<'ast>) -> TypeSolution {
        //main solver loop
        loop {
            let progress = self.solve_iter(types);
            if !progress { break; }
        }

        //map types back to cst types (and check that all types were indeed inferred)
        let state = (0..self.state.len()).map(|i| {
            let var = TypeVar(i);
            let ty = self.get_solution(types, var);

            let state = &self.state[i];
            let ty_info = &types[ty];
            if !self.state[i].post_check.is_satisfied_by(ty_info) {
                panic!(
                    "Type for {:?} with origin \n{:?}\nshould match {:?}, but was\n{:?} {:?}\n",
                    var, state.origin, state.post_check.to_short_string(), types[ty], ty_info,
                )
            }

            ty
        }).collect_vec();

        TypeSolution { state }
    }

    /// Run a single iteration of the solver, returns whether any progress was made.
    fn solve_iter(&mut self, types: &mut TypeStore<'ast>) -> bool {
        self.apply_index_constraints(types);
        self.apply_add_sub_constraints();

        //process all currently known matches
        // new ones (or ones that need to be kept) are appended to self.matches
        // they will be processed during the next iteration
        let matches = std::mem::take(&mut self.matches);
        let mut progress = false;
        for (left, right) in matches {
            progress |= self.unify_var(left, right);
        }
        progress
    }

    fn apply_index_constraints(&mut self, types: &mut TypeStore<'ast>) {
        let mut temp = std::mem::take(&mut self.index_constraints);

        temp.retain(|&IndexConstraint { target, result, index }| {
            let target = if let Some(target) = &self.state[target.0].info {
                target
            } else {
                //we don't know the target type yet, so we can't make progress
                return true;
            };

            match (target, index) {
                (TypeInfo::Tuple(target), IndexKind::Tuple(index)) => {
                    let target_result = target.fields.get(index as usize)
                        .expect("Tuple index out of bounds");
                    self.matches.push_back((*target_result, result))
                }
                (TypeInfo::Array(target), IndexKind::Array) => {
                    let target_result = target.inner;
                    self.matches.push_back((target_result, result))
                }
                (TypeInfo::Struct(target), IndexKind::Struct(index)) => {
                    let field_idx = target.find_field_index(index)
                        .unwrap_or_else(|| panic!("Struct {:?} does not have field {}", target, index));
                    let field_ty = target.fields[field_idx].ty;

                    let known_ty = self.fully_known(types, field_ty);
                    self.matches.push_back((result, known_ty));
                }
                (_, _) => panic!("Expected {} type, got {:?}", index.name(), target),
            }

            //we applied this constraint, it can now be removed
            false
        });

        assert!(self.index_constraints.is_empty());
        self.index_constraints = temp;
    }

    fn apply_add_sub_constraints(&mut self) {
        let mut temp = std::mem::take(&mut self.add_sub_constraints);

        temp.retain(|&AddSubConstraint { left, right }| {
            let left_info = if let Some(left) = &self.state[left.0].info {
                left
            } else {
                return true;
            };

            let required_right_ty = match left_info {
                &TypeInfo::Int(info) => self.known(Origin::FullyKnown, TypeInfo::Int(info)),
                TypeInfo::Pointer(_) => self.ty_isize,
                _ => panic!(
                    "Expected either pointer type or integer type for {:?} at {:?}, got {:?}",
                    left, self.state[0].origin, left_info
                )
            };

            self.matches.push_back((right, required_right_ty));
            false
        });

        assert!(self.add_sub_constraints.is_empty());
        self.add_sub_constraints = temp;
    }

    /// Get the type inferred for the given TypeVar.
    fn get_solution(&self, types: &mut TypeStore<'ast>, var: TypeVar) -> Type {
        let state = &self.state[var.0];
        if let Some(info) = &state.info {
            let info = info.map_ty(&mut |&var| self.get_solution(types, var));
            types.define_type(info)
        } else if state.default_void {
            types.type_void()
        } else {
            panic!("Failed to infer type for {:?} with origin {:?}", var, self.state[var.0].origin)
        }
    }

    /// Apply the requirement that both TypeVars match. Returns whether any progress was made.
    fn unify_var(&mut self, left: TypeVar, right: TypeVar) -> bool {
        let (left_state, right_state) = match self.state.index_mut_twice(left.0, right.0) {
            // both vars are the same, so nothing to do. also doesn't count as progress.
            None => return false,
            // they are different, continue
            Some(pair) => pair,
        };

        let mut progress = false;

        // propagate default_void if exactly one of them is true
        if left_state.default_void ^ right_state.default_void {
            progress |= true;
            left_state.default_void = true;
            right_state.default_void = true;
        }

        match (&left_state.info, &right_state.info) {
            (None, None) => {
                // we don't know enough to apply this match, so just keep it
                // no progress made
                self.matches.push_back((left, right));
            }
            (Some(left), None) => {
                // copy the entire info over
                right_state.info = Some(left.clone());
                progress |= true;
            }
            (None, Some(right)) => {
                // copy the entire info over
                left_state.info = Some(right.clone());
                progress |= true;
            }
            (Some(_), Some(_)) => {
                // unify the inner types if any
                self.unify_both_known(left, right);
                progress |= true;
            }
        }

        progress
    }

    /// Util function for `unify_var` that assumes both vars have known infos.
    fn unify_both_known(&mut self, left: TypeVar, right: TypeVar) {
        //TODO how to avoid cloning in this function?
        //TODO we really need to get some proper error handling in here that always reports the origin of things

        let left_info = self.state[left.0].info.as_ref().unwrap();
        let right_info = self.state[right.0].info.as_ref().unwrap();

        match (left_info, right_info) {
            (TypeInfo::Placeholder(_), _) | (_, TypeInfo::Placeholder(_)) => panic!("placeholder"),

            (TypeInfo::Void, TypeInfo::Void) => {}
            (TypeInfo::Bool, TypeInfo::Bool) => {}

            (&TypeInfo::Int(left_info), &TypeInfo::Int(right_info)) => {
                assert!(
                    left_info == right_info,
                    "Integer type mismatch between {:?}: {} and {:?}: {}",
                    left, left_info, right, right_info,
                );
            }

            (&TypeInfo::Pointer(left), &TypeInfo::Pointer(right)) => {
                self.unify_var(left, right);
            }
            (TypeInfo::Tuple(left), TypeInfo::Tuple(right)) => {
                assert_eq!(left.fields.len(), right.fields.len(), "tuples must have the same size");
                for (left, right) in zip_eq(left.fields.clone(), right.fields.clone()) {
                    self.unify_var(left, right);
                }
            }
            (TypeInfo::Function(left), TypeInfo::Function(right)) => {
                assert_eq!(left.params.len(), right.params.len(), "functions must have the same number of parameters");
                let left_ret = left.ret;
                let right_ret = right.ret;

                for (left, right) in zip_eq(left.params.clone(), right.params.clone()) {
                    self.unify_var(left, right);
                }

                //do this last so error messages appear more in order
                self.unify_var(left_ret, right_ret);
            }
            (TypeInfo::Array(left), TypeInfo::Array(right)) => {
                assert_eq!(left.length, right.length, "arrays must have the same length");
                let left_inner = left.inner;
                let right_inner = right.inner;
                self.unify_var(left_inner, right_inner);
            }

            (TypeInfo::Struct(left), TypeInfo::Struct(right)) => {
                assert_eq!(left, right)
            }

            _ => {
                panic!(
                    "Type mismatch: \n{:?}={:?} ({:?})\n{:?}={:?} ({:?})\n",
                    left, left_info, self.state[left.0].origin,
                    right, right_info, self.state[right.0].origin,
                )
            }
        }
    }
}

impl PostCheck {
    fn is_satisfied_by<T>(self, info: &TypeInfo<T>) -> bool {
        let (is_bool, is_int) = match info {
            TypeInfo::Bool => (true, None),
            TypeInfo::Int(info) => (false, Some(info.signed)),
            _ => (false, None)
        };

        let is_int_with_signedness = |expected: Option<Signed>| {
            match (is_int, expected) {
                (None, _) => false,
                (Some(_), None) => true,
                (Some(actual), Some(expected)) => actual == expected,
            }
        };

        match self {
            PostCheck::None => true,
            PostCheck::Int(signed) => is_int_with_signedness(signed),
            PostCheck::BoolOrInt(signed) => is_bool || is_int_with_signedness(signed),
        }
    }

    fn to_short_string(self) -> &'static str {
        match self {
            PostCheck::None => "",
            PostCheck::Int(None) => "i??/u??",
            PostCheck::Int(Some(Signed::Signed)) => "i??",
            PostCheck::Int(Some(Signed::Unsigned)) => "u??",
            PostCheck::BoolOrInt(None) => "bool/i??/u??",
            PostCheck::BoolOrInt(Some(Signed::Signed)) => "bool/i??",
            PostCheck::BoolOrInt(Some(Signed::Unsigned)) => "bool/u??",
        }
    }
}

impl std::ops::Index<TypeVar> for TypeSolution {
    type Output = Type;

    fn index(&self, index: TypeVar) -> &Self::Output {
        &self.state[index.0]
    }
}

impl<'ast> std::fmt::Debug for TypeProblem<'ast> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "TypeProblem {{\n    vars: [")?;

        for i in 0..self.state.len() {
            let var = TypeVar(i);
            let state = &self.state[i];

            let post_check = state.post_check.to_short_string();
            let default_void = match state.default_void {
                true => "->void",
                false => "",
            };

            writeln!(f, "        {:?}[{}{}]: {:?}, {:?}", var, post_check, default_void, state.info, state.origin)?;
        }

        writeln!(f, "    ],\n    constraints: [")?;
        for &(left, right) in &self.matches {
            writeln!(f, "        {:?} == {:?}", left, right)?;
        }

        writeln!(f, "    ],\n    index constraints: [")?;
        for &IndexConstraint { target, result, index } in &self.index_constraints {
            writeln!(f, "        {:?}[{:?}] == {:?}", target, index, result)?;
        }
        writeln!(f, "    ],")?;

        writeln!(f, "}}")?;

        Ok(())
    }
}

impl std::fmt::Debug for TypeSolution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "TypeSolution {{")?;

        for (i, &ty) in self.state.iter().enumerate() {
            let var = TypeVar(i);
            writeln!(f, "    {:?}: {:?}", var, ty)?;
        }

        writeln!(f, "}}")?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::front::ast::ExpressionKind;
    use crate::front::cst::TupleTypeInfo;
    use crate::front::pos::{FileId, Pos, Span};

    use super::*;

    macro_rules! setup {
        ($origin:ident, $types:ident, $problem:ident) => {
            let pos = Pos { file: FileId(0), line: 0, col: 0 };
            let expr = ast::Expression { span: Span { start: pos, end: pos }, kind: ExpressionKind::Null };
            let $origin = Origin::Expression(&expr);
            let mut $types = TypeStore::default();
            let mut $problem = TypeProblem::new(64);
        }
    }

    #[test]
    fn chain() {
        setup!(origin, types, problem);

        let (a, c, d) = (problem.unknown(origin), problem.unknown(origin), problem.unknown(origin));
        let b = problem.ty_bool();

        problem.equal(a, b);
        problem.equal(b, c);
        problem.equal(c, d);

        let sol = problem.solve(&mut types);
        for &var in &[a, b, c, d] {
            assert_eq!(types.type_bool(), sol[var]);
        }
    }

    #[test]
    fn tuple() {
        setup!(origin, types, problem);

        let (a, b) = (problem.ty_u8(), problem.unknown(origin));
        let (c, d) = (problem.unknown(origin), problem.ty_bool());

        let t1 = problem.known(origin, TypeInfo::Tuple(TupleTypeInfo { fields: vec![a, b] }));
        let t2 = problem.known(origin, TypeInfo::Tuple(TupleTypeInfo { fields: vec![c, d] }));
        problem.equal(t1, t2);

        let sol = problem.solve(&mut types);

        let tuple_info = TupleTypeInfo { fields: vec![types.type_u8(), types.type_bool()] };
        let type_tuple = types.define_type(TypeInfo::Tuple(tuple_info));
        assert_eq!(types.type_u8(), sol[a]);
        assert_eq!(types.type_u8(), sol[c]);
        assert_eq!(types.type_bool(), sol[b]);
        assert_eq!(types.type_bool(), sol[d]);
        assert_eq!(type_tuple, sol[t1]);
        assert_eq!(type_tuple, sol[t2]);
    }

    #[test]
    fn ptr_ptr() {
        setup!(origin, types, problem);

        let a = problem.unknown(origin);
        let a_ptr = problem.known(origin, TypeInfo::Pointer(a));
        let b = problem.unknown(origin);
        let b_ptr = problem.known(origin, TypeInfo::Pointer(b));

        problem.equal(a_ptr, b_ptr);
        problem.equal(problem.ty_u8(), b);

        let sol = problem.solve(&mut types);

        assert_eq!(types.type_u8(), sol[a]);
        assert_eq!(types.type_u8(), sol[b]);
        assert_eq!(types.define_type_ptr(types.type_u8()), sol[a_ptr]);
        assert_eq!(types.define_type_ptr(types.type_u8()), sol[b_ptr]);
    }

    #[test]
    fn default_void_propagate() {
        setup!(origin, types, problem);

        let a = problem.unknown(origin);
        let b = problem.unknown_default_void(origin);
        let c = problem.unknown(origin);
        let d = problem.unknown(origin);
        problem.equal(a, b);
        problem.equal(b, c);
        problem.equal(c, d);

        let sol = problem.solve(&mut types);
        assert_eq!(types.type_void(), sol[a]);
        assert_eq!(types.type_void(), sol[b]);
        assert_eq!(types.type_void(), sol[c]);
        assert_eq!(types.type_void(), sol[d]);
    }
}
