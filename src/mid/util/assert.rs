use crate::mid::ir::Program;
use crate::mid::util::verify::{TypeOrValue, TypeString};

#[track_caller]
pub fn assert_type_match(prog: &Program, left: impl Into<TypeOrValue>, right: impl Into<TypeOrValue>) {
    let left = left.into();
    let right = right.into();

    let left_ty = left.ty(prog);
    let right_ty = right.ty(prog);

    assert_eq!(left_ty, right_ty, "Expected type match between {:?} and {:?}, got {:?} and {:?}", left, right, TypeString::new(prog, left_ty), TypeString::new(prog, right_ty));
}