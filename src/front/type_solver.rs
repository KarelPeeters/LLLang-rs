use std::collections::VecDeque;

use itertools::zip;

use crate::front::cst;
use crate::front::cst::{FunctionTypeInfo, TupleTypeInfo, TypeStore};

type TypeInfo = cst::TypeInfo<TypeVar, cst::Type>;

/// Represents the type of an expression in the program.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct TypeVar(usize);

#[derive(Default)]
struct TypeProblem {
    state: Vec<Option<TypeInfo>>,
    matches: Vec<(TypeVar, TypeVar)>,
}

struct TypeSolution {
    state: Vec<Option<TypeInfo>>
}

impl TypeProblem {
    pub fn unknown(&mut self) -> TypeVar {
        let i = self.state.len();
        self.state.push(None);
        TypeVar(i)
    }

    pub fn known(&mut self, info: TypeInfo) -> TypeVar {
        let i = self.state.len();
        self.state.push(Some(info));
        TypeVar(i)
    }

    pub fn same(&mut self, left: TypeVar, right: TypeVar) {
        self.matches.push((left, right))
    }

    pub fn solve(self) -> TypeSolution {
        let mut solver = Solver { state: self.state };
        solver.solve(self.matches.into());

        //verify that everything was resolved
        for info in &solver.state {
            assert!(info.is_some())
        }

        return TypeSolution { state: solver.state };
    }
}

impl std::ops::Index<TypeVar> for TypeSolution {
    type Output = TypeInfo;

    fn index(&self, index: TypeVar) -> &Self::Output {
        self.state[index.0].as_ref().unwrap()
    }
}

impl TypeSolution {
    //TODO should this function be defined in TypeSolution? it has to do with cst::Type so that's kind of scrappy
    fn map(&self, store: &mut TypeStore, var: TypeVar) -> cst::Type {
        assert!(var.0 < self.state.len(), "{:?} does not belong to this solution", var);

        match self.state[var.0].as_ref().unwrap() {
            TypeInfo::Placeholder(_) => panic!("placeholder"),
            TypeInfo::Void => store.type_void(),
            TypeInfo::Bool => store.type_bool(),
            TypeInfo::Byte => store.type_byte(),
            TypeInfo::Int => store.type_int(),
            TypeInfo::Pointer(inner) => {
                let inner = self.map(store, *inner);
                store.define_type_ptr(inner)
            }
            TypeInfo::Tuple(info) => {
                let fields: Vec<cst::Type> = info.fields.iter().map(|&v| self.map(store, v)).collect();
                store.define_type(cst::TypeInfo::Tuple(TupleTypeInfo { fields }))
            }
            TypeInfo::Function(info) => {
                let params: Vec<cst::Type> = info.params.iter().map(|&v| self.map(store, v)).collect();
                let ret = self.map(store, info.ret);
                store.define_type(cst::TypeInfo::Function(FunctionTypeInfo { params, ret }))
            }
            TypeInfo::Struct(info) => *info,
        }
    }
}

struct Solver {
    state: Vec<Option<TypeInfo>>,
}

//todo don't assert anywhere, return an error instead
impl Solver {
    fn solve(&mut self, mut matches: VecDeque<(TypeVar, TypeVar)>) {
        loop {
            let mut any_progress = false;

            matches.retain(|&(left, right)| {
                if left == right {
                    false
                } else {
                    let applied = self.unify_var(left, right);
                    any_progress |= applied;
                    !applied
                }
            });

            if !any_progress { break }
        }
    }

    /// Returns whether this match was fully applied and can be removed
    fn unify_var(&mut self, left: TypeVar, right: TypeVar) -> bool {
        assert_ne!(left, right);

        match (&self.state[left.0], &self.state[right.0]) {
            //todo we need to revisit this later, record it somewhere?
            (None, None) => false,
            (Some(left), None) => {
                self.state[right.0] = Some(left.clone());
                true
            }
            (None, Some(right)) => {
                self.state[left.0] = Some(right.clone());
                true
            }
            (Some(_), Some(_)) => {
                self.unify_both_known(left, right);
                true
            }
        }
    }

    fn unify_both_known(&mut self, left: TypeVar, right: TypeVar) {
        //TODO how to avoid cloning in this function?

        let left = self.state[left.0].as_ref().unwrap();
        let right = self.state[right.0].as_ref().unwrap();

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
                assert_eq!(left.fields.len(), right.fields.len());
                for (left, right) in zip(left.fields.clone(), right.fields.clone()) {
                    self.unify_var(left, right);
                }
            }
            (TypeInfo::Function(left), TypeInfo::Function(right)) => {
                assert_eq!(left.params.len(), right.params.len());
                let (left_ret, right_ret) = (left.ret, right.ret);
                for (left, right) in zip(left.params.clone(), right.params.clone()) {
                    self.unify_var(left, right);
                }

                //do this last so error messages appear more in order
                self.unify_var(left_ret, right_ret);
            }

            (TypeInfo::Struct(left), TypeInfo::Struct(right)) => {
                assert_eq!(left, right)
            }

            _ => {
                panic!("Trying to unify structurally different types")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_chain() {
        let mut problem = TypeProblem::default();
        let (a, c, d) = (problem.unknown(), problem.unknown(), problem.unknown());
        let b = problem.known(TypeInfo::Int);

        problem.same(a, b);
        problem.same(b, c);
        problem.same(c, d);

        let sol = problem.solve();
        for &var in &[a, b, c, d] {
            assert_eq!(TypeInfo::Int, sol[var]);
        }
    }

    #[test]
    fn trough_tuple() {
        let mut problem = TypeProblem::default();
        let (a, b) = (problem.known(TypeInfo::Int), problem.unknown());
        let (c, d) = (problem.unknown(), problem.known(TypeInfo::Bool));

        let t1 = problem.known(TypeInfo::Tuple(TupleTypeInfo { fields: vec![a, b] }));
        let t2 = problem.known(TypeInfo::Tuple(TupleTypeInfo { fields: vec![c, d] }));
        problem.same(t1, t2);

        let sol = problem.solve();
        assert_eq!(TypeInfo::Int, sol[a]);
        assert_eq!(TypeInfo::Int, sol[c]);
        assert_eq!(TypeInfo::Bool, sol[b]);
        assert_eq!(TypeInfo::Bool, sol[d]);
    }
}
