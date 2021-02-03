use std::collections::VecDeque;
use std::fmt::Formatter;

use itertools::{Itertools, zip};

use crate::front::cst;
use crate::front::cst::{Type, TypeInfo, TypeStore};

type VarTypeInfo<'ast> = cst::TypeInfo<'ast, TypeVar>;
type KnownTypeInfo<'ast> = cst::TypeInfo<'ast, Type>;

/// Represents the type of an expression in the program.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct TypeVar(usize);

#[derive(Copy, Clone, Eq, PartialEq)]
enum Property {
    Unknown,
    AnyInt,
    DefaultVoid,
}

//TODO don't assert anywhere, return an error instead. look at unwrap, expect, panic, ...
//TODO print out an instance once, to see how much duplicate noise there is
pub struct TypeProblem<'ast> {
    state: Vec<(Option<VarTypeInfo<'ast>>, Property)>,

    matches: VecDeque<(TypeVar, TypeVar)>,
    struct_index: VecDeque<(TypeVar, &'ast str, TypeVar)>,
    tuple_index: VecDeque<(TypeVar, u32, TypeVar)>,

    //basic types
    ty_void: TypeVar,
    ty_bool: TypeVar,
    ty_byte: TypeVar,
}

pub struct TypeSolution {
    state: Vec<Type>
}

impl<'ast> Default for TypeProblem<'ast> {
    fn default() -> Self {
        let mut result = TypeProblem {
            state: Default::default(),
            matches: Default::default(),
            struct_index: Default::default(),
            tuple_index: Default::default(),

            ty_void: TypeVar(0),
            ty_bool: TypeVar(0),
            ty_byte: TypeVar(0),
        };
        result.ty_void = result.known(TypeInfo::Void);
        result.ty_bool = result.known(TypeInfo::Bool);
        result.ty_byte = result.known(TypeInfo::Byte);
        result
    }
}

impl<'ast> TypeProblem<'ast> {
    fn new_var(&mut self, prop: Property) -> TypeVar {
        let i = self.state.len();
        self.state.push((None, prop));
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

    /// Create a new TypeVar without any known type information.
    pub fn unknown(&mut self) -> TypeVar {
        self.new_var(Property::Unknown)
    }

    /// Create a new TypeVar without a known type, but that gets assigned the void type if at the end of inference this
    /// type still has no inferred type.
    pub fn unknown_default_void(&mut self) -> TypeVar {
        self.new_var(Property::DefaultVoid)
    }

    /// Create a new TypeVar that can be assigned any integer type.
    pub fn unknown_int(&mut self) -> TypeVar {
        self.new_var(Property::AnyInt)
    }

    /// Create a new TypeVar with a known type pattern
    pub fn known(&mut self, info: VarTypeInfo<'ast>) -> TypeVar {
        let var = self.unknown();

        //TODO this is easy to forget, is there a better way to handle this
        if let TypeInfo::Wildcard = info {
            return var;
        }

        self.state[var.0].0 = Some(info);
        var
    }

    /// Create a new TypeVar with a fully known type.
    pub fn fully_known(&mut self, types: &cst::TypeStore<'ast>, ty: Type) -> TypeVar {
        let info = types[ty].map_ty(&mut |&child_ty| self.fully_known(types, child_ty));
        self.known(info)
    }

    /// Create a new TypeVar representing the type of a tuple index expression.
    pub fn tuple_index(&mut self, target: TypeVar, index: u32) -> TypeVar {
        let var = self.unknown();
        self.tuple_index.push_back((target, index, var));
        var
    }

    /// Create a new TypeVar representing the type of a struct index expression.
    pub fn struct_index(&mut self, target: TypeVar, index: &'ast str) -> TypeVar {
        let var = self.unknown();
        self.struct_index.push_back((target, index, var));
        var
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
        let mut fully_known_queue = Vec::new();
        loop {
            let progress = self.solve_iter(types, &mut fully_known_queue);
            if !progress { break; }
        }

        //map types back to cst types (and check that all types were indeed inferred)
        let state = (0..self.state.len()).map(|i| {
            let ty = self.get_solution(types, TypeVar(i));

            //check that integer requirements are satisfied
            if self.state[i].1 == Property::AnyInt {
                assert!(matches!(self.state[i].0.as_ref().unwrap(), TypeInfo::Byte | TypeInfo::Int))
            }

            ty
        }).collect_vec();

        TypeSolution { state }
    }

    /// Run a single iteration of the solver, returns whether any progress was made.
    fn solve_iter(&mut self, types: &mut TypeStore<'ast>, fully_known_queue: &mut Vec<(TypeVar, Type)>) -> bool {
        let state = &self.state;
        let matches = &mut self.matches;

        self.tuple_index.retain(|&(target, index, result)| {
            if let Some(target) = &state[target.0].0 {
                if let TypeInfo::Tuple(target) = target {
                    let target_result = target.fields.get(index as usize)
                        .expect("Tuple index out of bounds");
                    matches.push_back((*target_result, result))
                } else {
                    panic!("Expected tuple type, got {:?}", target);
                }

                false
            } else {
                true
            }
        });

        self.struct_index.retain(|&(target, index, result)| {
            if let Some(target) = &state[target.0].0 {
                if let TypeInfo::Struct(target) = target {
                    let (_, field_ty) = target.fiend_field(index).unwrap();
                    fully_known_queue.push((result, field_ty));
                } else {
                    panic!("Expected struct type, got {:?}", target);
                }

                false
            } else {
                true
            }
        });

        for &(result, field_ty) in fully_known_queue.iter() {
            let field_ty = self.fully_known(types, field_ty);
            self.matches.push_back((field_ty, result))
        }
        fully_known_queue.clear();

        let mut progress = false;

        let mut matches = std::mem::take(&mut self.matches);
        matches.retain(|&(left, right)| {
            if left == right {
                false
            } else {
                let applied = self.unify_var(left, right);
                progress |= applied;
                !applied
            }
        });

        //make sure no other code added stuff to this temporary vec
        assert!(self.matches.is_empty());
        self.matches = matches;

        progress
    }

    /// Get the type inferred for the given TypeVar.
    fn get_solution(&self, types: &mut TypeStore<'ast>, var: TypeVar) -> Type {
        let state = &self.state[var.0];
        if let Some(info) = &state.0 {
            let info = info.map_ty(&mut |&var| self.get_solution(types, var));
            types.define_type(info)
        } else if state.1 == Property::DefaultVoid {
            types.type_void()
        } else {
            panic!("Failed to infer type for {:?}", var)
        }
    }

    /// Apply the requirement that both TypeVars match. Returns whether this match was fully applied and doesn't need to
    /// be considered again.
    fn unify_var(&mut self, left: TypeVar, right: TypeVar) -> bool {
        //nothing to do, skip
        if left == right {
            return true
        }

        match (&self.state[left.0].0, &self.state[right.0].0) {
            //todo we need to revisit this later, record it somewhere?
            (None, None) => false,
            (Some(left), None) => {
                self.state[right.0].0 = Some(left.clone());
                true
            }
            (None, Some(right)) => {
                self.state[left.0].0 = Some(right.clone());
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

        let left = self.state[left.0].0.as_ref().unwrap();
        let right = self.state[right.0].0.as_ref().unwrap();

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

            let prop = match state.1 {
                Property::Unknown => "",
                Property::AnyInt => "int",
                Property::DefaultVoid => "->void",
            };

            writeln!(f, "        {:?}({}): {:?}", var, prop, state.0)?;
        }

        writeln!(f, "    ],\n    constraints: [")?;

        for &(left, right) in &self.matches {
            writeln!(f, "        {:?} == {:?}", left, right)?;
        }

        for &(target, index, result) in &self.tuple_index {
            writeln!(f, "        {:?}.{} == {:?}", target, index, result)?;
        }

        for &(target, index, result) in &self.struct_index {
            writeln!(f, "        {:?}.{} == {:?}", target, index, result)?;
        }

        write!(f, "    ]\n}}\n")?;
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
    use crate::front::cst::TupleTypeInfo;

    use super::*;

    #[test]
    fn chain() {
        let mut types = TypeStore::default();
        let mut problem = TypeProblem::default();
        let (a, c, d) = (problem.unknown(), problem.unknown(), problem.unknown());
        let b = problem.known(TypeInfo::Int);

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
        let mut types = TypeStore::default();
        let mut problem = TypeProblem::default();
        let (a, b) = (problem.known(TypeInfo::Int), problem.unknown());
        let (c, d) = (problem.unknown(), problem.known(TypeInfo::Bool));

        let t1 = problem.known(TypeInfo::Tuple(TupleTypeInfo { fields: vec![a, b] }));
        let t2 = problem.known(TypeInfo::Tuple(TupleTypeInfo { fields: vec![c, d] }));
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
}
