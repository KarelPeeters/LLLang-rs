use crate::mid::ir::{Type, Value};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Lattice {
    Undef,
    Known(Value),
    Overdef,
}

impl Lattice {
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

    pub fn as_value_of_type(self, ty: Type) -> Option<Value> {
        match self {
            Lattice::Undef => Some(Value::Undef(ty)),
            Lattice::Known(value) => Some(value),
            Lattice::Overdef => None,
        }
    }
}
