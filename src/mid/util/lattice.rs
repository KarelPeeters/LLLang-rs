use crate::mid::ir::{Const, Program, Type, Value};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Lattice {
    Undef,
    Known(Value),
    Overdef,
}

impl Lattice {
    pub fn fold(values: impl IntoIterator<Item=Lattice>) -> Lattice {
        values.into_iter().fold(Lattice::Undef, Lattice::merge)
    }

    pub fn merge(left: Lattice, right: Lattice) -> Lattice {
        match (left, right) {
            (Lattice::Overdef, _) | (_, Lattice::Overdef) =>
                Lattice::Overdef,
            (Lattice::Undef, other) | (other, Lattice::Undef) =>
                other,
            (Lattice::Known(left), Lattice::Known(right)) =>
                if left == right { Lattice::Known(left) } else { Lattice::Overdef },
        }
    }

    pub fn as_value_of_type(self, prog: &Program, ty: Type) -> Option<Value> {
        if ty == prog.ty_void() {
            return Some(Value::Void);
        }

        match self {
            Lattice::Undef => Some(Value::Undef(ty)),
            Lattice::Known(value) => Some(value),
            Lattice::Overdef => None,
        }
    }

    pub fn map_known(self, f: impl FnOnce(Value) -> Lattice) -> Lattice {
        match self {
            Lattice::Undef => Lattice::Undef,
            Lattice::Known(value) => f(value),
            Lattice::Overdef => Lattice::Overdef,
        }
    }

    pub fn map_known_const(self, f: impl FnOnce(Const) -> Lattice) -> Lattice {
        match self {
            Lattice::Undef => Lattice::Undef,
            Lattice::Known(Value::Const(cst)) => f(cst),
            Lattice::Known(_) => Lattice::Overdef,
            Lattice::Overdef => Lattice::Overdef,
        }
    }
}
