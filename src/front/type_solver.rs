//TODO actually start using this in lower_func!
pub struct TypeProblem<T> {
    var_count: usize,
    known_constraints: Vec<(TypeVar, T)>,
    match_constraints: Vec<(TypeVar, TypeVar)>,
}

pub struct TypeSolution<T> {
    result: Vec<T>,
}

pub enum TypeError<T> {
    TypeMismatch(TypeVar, T, T),
    TypeConflict(TypeVar, TypeVar, T, T),
    CannotInfer(TypeVar),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVar(usize);

impl<T: Copy + Eq> TypeProblem<T> {
    pub fn new_var(&mut self) -> TypeVar {
        let i = self.var_count;
        self.var_count += 1;
        TypeVar(i)
    }

    pub fn add_constraint_known(&mut self, var: TypeVar, ty: T) {
        self.known_constraints.push((var, ty));
    }

    pub fn add_constraint_match(&mut self, left: TypeVar, right: TypeVar) {
        self.match_constraints.push((left, right))
    }

    pub fn solve(&self) -> Result<TypeSolution<T>, TypeError<T>> {
        let mut result: Vec<Option<T>> = vec![None; self.var_count];

        //set all known types
        for &(var, ty) in &self.known_constraints {
            match result[var.0] {
                None => { result[var.0] = Some(ty) }
                Some(prev_ty) if prev_ty != ty => {
                    return Err(TypeError::TypeMismatch(var, prev_ty, ty));
                }
                Some(_) => {}
            }
        }

        //propagate matches until fixpoint
        //TODO this is stupid, there should a proper/faster way to do this
        loop {
            let mut changed = false;

            for &(left_var, right_var) in &self.match_constraints {
                match (result[left_var.0], result[right_var.0]) {
                    (Some(left_ty), Some(right_ty)) => {
                        if left_ty != right_ty {
                            return Err(TypeError::TypeConflict(left_var, right_var, left_ty, right_ty));
                        }
                    }
                    (Some(known_ty), None) | (None, Some(known_ty)) => {
                        result[left_var.0] = Some(known_ty);
                        result[right_var.0] = Some(known_ty);
                        changed = true;
                    }
                    (None, None) => {}
                }
            }

            if !changed { break; }
        }

        //check that all vars were inferred
        let result = result.iter().enumerate()
            .map(|(i, x)| x.ok_or(TypeError::CannotInfer(TypeVar(i))))
            .collect::<Result<_, _>>()?;

        Ok(TypeSolution { result })
    }
}

impl<T> std::ops::Index<TypeVar> for TypeSolution<T> {
    type Output = T;

    fn index(&self, index: TypeVar) -> &Self::Output {
        assert!(index.0 < self.result.len(), "variable {:?} was not registered to this solution", index);
        &self.result[index.0]
    }
}
