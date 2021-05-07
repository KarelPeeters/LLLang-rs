use std::collections::VecDeque;
use std::fmt::Formatter;

use itertools::Itertools;

use crate::front::{ast, cst};
use crate::front::cst::{Type, TypeInfo, TypeStore};
use crate::util::zip_eq;

type VarTypeInfo<'ast> = cst::TypeInfo<'ast, TypeVar>;

/// Represents the type of an expression in the program.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct TypeVar(usize);

#[derive(Debug)]
struct VarState<'ast> {
    origin: Origin<'ast>,
    constraint: Constraint,
    info: Option<VarTypeInfo<'ast>>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Constraint {
    None,
    AnyInt,
    DefaultVoid,
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
    index_matches: VecDeque<IndexMatch<'ast>>,

    //basic types
    ty_void: TypeVar,
    ty_bool: TypeVar,
    ty_byte: TypeVar,
    ty_int: TypeVar,
}

pub struct TypeSolution {
    state: Vec<Type>,
}

#[derive(Debug, Copy, Clone)]
struct IndexMatch<'ast> {
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

impl<'ast> Default for TypeProblem<'ast> {
    fn default() -> Self {
        let mut problem = TypeProblem {
            state: vec![],
            matches: Default::default(),
            index_matches: Default::default(),

            ty_void: TypeVar(usize::MAX),
            ty_bool: TypeVar(usize::MAX),
            ty_byte: TypeVar(usize::MAX),
            ty_int: TypeVar(usize::MAX),
        };

        problem.ty_void = problem.known(Origin::FullyKnown, TypeInfo::Void);
        problem.ty_bool = problem.known(Origin::FullyKnown, TypeInfo::Bool);
        problem.ty_byte = problem.known(Origin::FullyKnown, TypeInfo::Byte);
        problem.ty_int = problem.known(Origin::FullyKnown, TypeInfo::Int);

        problem
    }
}

impl<'ast> TypeProblem<'ast> {
    /// The current amount of `TypeVar`s defined in this problem.
    pub fn len(&self) -> usize {
        self.state.len()
    }

    fn new_var(&mut self, origin: Origin<'ast>, constraint: Constraint, info: Option<VarTypeInfo<'ast>>) -> TypeVar {
        // Some(Wildcard) means that we don't know anything about a type, so convert it to None
        let info = info.filter(|info| info != &VarTypeInfo::Wildcard);

        let i = self.state.len();
        self.state.push(VarState { origin, constraint, info });
        TypeVar(i)
    }

    pub fn ty_void(&self) -> TypeVar {
        self.ty_void
    }

    pub fn ty_bool(&self) -> TypeVar {
        self.ty_bool
    }

    pub fn ty_byte(&self) -> TypeVar {
        self.ty_byte
    }

    pub fn ty_int(&self) -> TypeVar {
        self.ty_int
    }

    /// Create a new TypeVar without any known type information.
    pub fn unknown(&mut self, origin: Origin<'ast>) -> TypeVar {
        self.new_var(origin, Constraint::None, None)
    }

    /// Create a new TypeVar without a known type, but that gets assigned the void type if at the end of inference this
    /// type still has no inferred type.
    pub fn unknown_default_void(&mut self, origin: Origin<'ast>) -> TypeVar {
        self.new_var(origin, Constraint::DefaultVoid, None)
    }

    /// Create a new TypeVar that can be assigned any integer type.
    pub fn unknown_int(&mut self, origin: Origin<'ast>) -> TypeVar {
        self.new_var(origin, Constraint::AnyInt, None)
    }

    /// Create a new TypeVar with a known type pattern
    pub fn known(&mut self, origin: Origin<'ast>, info: VarTypeInfo<'ast>) -> TypeVar {
        self.new_var(origin, Constraint::None, Some(info))
    }

    /// Create a new TypeVar with a fully known type.
    pub fn fully_known(&mut self, types: &cst::TypeStore<'ast>, ty: Type) -> TypeVar {
        let info = types[ty].map_ty(&mut |&child_ty| {
            self.fully_known(types, child_ty)
        });
        self.known(Origin::FullyKnown, info)
    }

    /// Create a new TypeVar representing the type of a tuple index expression.
    pub fn tuple_index(&mut self, origin: Origin<'ast>, target: TypeVar, index: u32) -> TypeVar {
        let result = self.unknown(origin);
        self.index_matches.push_back(IndexMatch { target, result, index: IndexKind::Tuple(index) });
        result
    }

    /// Create a new TypeVar representing the type of a struct index expression.
    pub fn struct_index(&mut self, origin: Origin<'ast>, target: TypeVar, index: &'ast str) -> TypeVar {
        let result = self.unknown(origin);
        self.index_matches.push_back(IndexMatch { target, result, index: IndexKind::Struct(index) });
        result
    }

    /// Create a new TypeVar representing the result type of an array index expression.
    pub fn array_index(&mut self, origin: Origin<'ast>, target: TypeVar) -> TypeVar {
        let result = self.unknown(origin);
        self.index_matches.push_back(IndexMatch { target, result, index: IndexKind::Array });
        result
    }

    /// Require that two types match
    pub fn equal(&mut self, left: TypeVar, right: TypeVar) {
        self.matches.push_back((left, right))
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

            //check that integer requirements are satisfied
            if self.state[i].constraint == Constraint::AnyInt {
                let info = &types[ty];

                match info {
                    TypeInfo::Byte | TypeInfo::Int => {}
                    _ => panic!(
                        "Type for {:?} with origin \n{:?}\nshould be an integer, but was\n{:?}\n",
                        var, self.state[var.0].origin, info,
                    ),
                }
            }

            ty
        }).collect_vec();

        TypeSolution { state }
    }

    /// Run a single iteration of the solver, returns whether any progress was made.
    fn solve_iter(&mut self, types: &mut TypeStore<'ast>) -> bool {
        self.apply_index_constraints(types);

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
        let mut index_matches = std::mem::take(&mut self.index_matches);

        index_matches.retain(|&IndexMatch { target, result, index }| {
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
                    let field_ty = target.fields[field_idx as usize].ty;

                    let known_ty = self.fully_known(types, field_ty);
                    self.matches.push_back((result, known_ty));
                }
                (_, _) => panic!("Expected {} type, got {:?}", index.name(), target),
            }

            //we applied this constraint, it can now be removed
            false
        });

        assert!(self.index_matches.is_empty());
        self.index_matches = index_matches;
    }

    /// Get the type inferred for the given TypeVar.
    fn get_solution(&self, types: &mut TypeStore<'ast>, var: TypeVar) -> Type {
        let state = &self.state[var.0];
        if let Some(info) = &state.info {
            let info = info.map_ty(&mut |&var| self.get_solution(types, var));
            types.define_type(info)
        } else if state.constraint == Constraint::DefaultVoid {
            types.type_void()
        } else {
            panic!("Failed to infer type for {:?} with origin {:?}", var, self.state[var.0].origin)
        }
    }

    /// Apply the requirement that both TypeVars match. Returns whether any progress was made.
    fn unify_var(&mut self, left: TypeVar, right: TypeVar) -> bool {
        //nothing to do, skip. also doesn't count as progress.
        if left == right { return false; }

        match (&self.state[left.0].info, &self.state[right.0].info) {
            (None, None) => {
                // we don't know enough to apply this match, so just keep it
                self.matches.push_back((left, right));
                false
            }
            (Some(left), None) => {
                self.state[right.0].info = Some(left.clone());
                true
            }
            (None, Some(right)) => {
                self.state[left.0].info = Some(right.clone());
                true
            }
            (Some(_), Some(_)) => {
                self.unify_both_known(left, right);
                true
            }
        }
    }

    /// Util function for `unify_var` that assumes both vars have known infos.
    fn unify_both_known(&mut self, left: TypeVar, right: TypeVar) {
        //TODO how to avoid cloning in this function?

        let left = self.state[left.0].info.as_ref().unwrap();
        let right = self.state[right.0].info.as_ref().unwrap();

        match (left, right) {
            (TypeInfo::Placeholder(_), _) | (_, TypeInfo::Placeholder(_)) => panic!("placeholder"),

            (TypeInfo::Void, TypeInfo::Void) => {}
            (TypeInfo::Bool, TypeInfo::Bool) => {}
            (TypeInfo::Byte, TypeInfo::Byte) => {}
            (TypeInfo::Int, TypeInfo::Int) => {}

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
                panic!("Type mismatch: {:?} and {:?}", left, right)
            }
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
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "TypeProblem {{\n    vars: [")?;

        for i in 0..self.state.len() {
            let var = TypeVar(i);
            let state = &self.state[i];

            let constraint = match state.constraint {
                Constraint::None => "",
                Constraint::AnyInt => "int",
                Constraint::DefaultVoid => "->void",
            };

            writeln!(f, "        {:?}[{}]: {:?}, {:?}", var, constraint, state.info, state.origin)?;
        }

        writeln!(f, "    ],\n    constraints: [")?;
        for &(left, right) in &self.matches {
            writeln!(f, "        {:?} == {:?}", left, right)?;
        }

        writeln!(f, "    ],\n    index constraints: [")?;
        for &IndexMatch { target, result, index } in &self.index_matches {
            writeln!(f, "        {:?}[{:?}] == {:?}", target, index, result)?;
        }
        writeln!(f, "    ],")?;

        writeln!(f, "}}")?;

        Ok(())
    }
}

impl std::fmt::Debug for TypeSolution {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

    fn dummy_expr() -> ast::Expression {
        let pos = Pos { file: FileId(0), line: 0, col: 0 };
        ast::Expression { span: Span { start: pos, end: pos }, kind: ExpressionKind::Null }
    }

    #[test]
    fn chain() {
        let expr = dummy_expr();
        let origin = Origin::Expression(&expr);

        let mut types = TypeStore::default();
        let mut problem = TypeProblem::default();
        let (a, c, d) = (problem.unknown(origin), problem.unknown(origin), problem.unknown(origin));
        let b = problem.known(Origin::FullyKnown, TypeInfo::Int);

        problem.equal(a, b);
        problem.equal(b, c);
        problem.equal(c, d);

        let sol = problem.solve(&mut types);
        for &var in &[a, b, c, d] {
            assert_eq!(types.type_int(), sol[var]);
        }
    }

    #[test]
    fn tuple() {
        let expr = dummy_expr();
        let origin = Origin::Expression(&expr);

        let mut types = TypeStore::default();
        let mut problem = TypeProblem::default();
        let (a, b) = (problem.known(origin, TypeInfo::Int), problem.unknown(origin));
        let (c, d) = (problem.unknown(origin), problem.known(origin, TypeInfo::Bool));

        let t1 = problem.known(origin, TypeInfo::Tuple(TupleTypeInfo { fields: vec![a, b] }));
        let t2 = problem.known(origin, TypeInfo::Tuple(TupleTypeInfo { fields: vec![c, d] }));
        problem.equal(t1, t2);

        let sol = problem.solve(&mut types);

        let tuple_info = TupleTypeInfo { fields: vec![types.type_int(), types.type_bool()] };
        let type_tuple = types.define_type(TypeInfo::Tuple(tuple_info));
        assert_eq!(types.type_int(), sol[a]);
        assert_eq!(types.type_int(), sol[c]);
        assert_eq!(types.type_bool(), sol[b]);
        assert_eq!(types.type_bool(), sol[d]);
        assert_eq!(type_tuple, sol[t1]);
        assert_eq!(type_tuple, sol[t2]);
    }

    #[test]
    fn ptr_ptr() {
        let expr = dummy_expr();
        let origin = Origin::Expression(&expr);

        let mut types = TypeStore::default();
        let mut problem = TypeProblem::default();

        let a = problem.unknown(origin);
        let a_ptr = problem.known(origin, TypeInfo::Pointer(a));
        let b = problem.unknown(origin);
        let b_ptr = problem.known(origin, TypeInfo::Pointer(b));

        problem.equal(a_ptr, b_ptr);
        problem.equal(problem.ty_byte(), b);

        let sol = problem.solve(&mut types);

        assert_eq!(types.type_byte(), sol[a]);
        assert_eq!(types.type_byte(), sol[b]);
        assert_eq!(types.define_type_ptr(types.type_byte()), sol[a_ptr]);
        assert_eq!(types.define_type_ptr(types.type_byte()), sol[b_ptr]);
    }
}
