use crate::mid::ir;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum Lattice<V> {
    Undef,
    Known(V),
    Overdef,
}

impl <V: Eq> Lattice<V> {
    pub fn merge(left: Self, right: Self) -> Self {
        match (left, right) {
            (Lattice::Overdef, _) | (_, Lattice::Overdef) =>
                Lattice::Overdef,
            (Lattice::Undef, other) | (other, Lattice::Undef) =>
                other,
            (Lattice::Known(left), Lattice::Known(right)) =>
                if left == right { Lattice::Known(left) } else { Lattice::Overdef },
        }
    }

    pub fn fold(iter: impl IntoIterator<Item=Self>) -> Self {
        iter.into_iter().fold(Lattice::Undef, Self::merge)
    }
}

impl Lattice<ir::Value> {
    pub fn as_value_of_type(self, ty: ir::Type) -> Option<ir::Value> {
        match self {
            Lattice::Undef => Some(ir::Value::Undef(ty)),
            Lattice::Known(value) => {
                assert!(value.is_const_like());
                Some(value)
            }
            Lattice::Overdef => None,
        }
    }
}