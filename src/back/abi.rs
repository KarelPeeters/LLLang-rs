use crate::back::register::Register;
use crate::back::register::Register::*;

// TODO use some proper ABI settings, maybe depending on the platform?
// TODO caller and callee saved? do we need distinctions between preferred and not or will it figure it out itself
//   when calls clobber stuff?

// TODO do we really need to blacklist bp if we don't use it?
pub const SPECIAL_PURPOSE_REGS: &[Register] = &[
    BP,
    SP,
];

// TODO this to many registers, only the first 4 are actually right
pub const ABI_PARAM_REGS: &[Register] = &[C, D, R8, R9, R10, R11];
pub const ABI_RETURN_REG: Register = A;

#[allow(dead_code)]
pub const ABI_CALL_VOLATILE_REGS: &[Register] = &[A, C, D, R8, R9, R10, R11];
#[allow(dead_code)]
pub const ABI_CALL_NON_VOLATILE_REGS: &[Register] = &[B, BP, DI, SI, SP, R12, R13, R14, R15];

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use crate::back::abi::{ABI_CALL_NON_VOLATILE_REGS, ABI_CALL_VOLATILE_REGS, ABI_PARAM_REGS, SPECIAL_PURPOSE_REGS};
    use crate::back::register::Register;

    #[test]
    fn makes_sense() {
        assert_eq!(SPECIAL_PURPOSE_REGS.to_vec(), SPECIAL_PURPOSE_REGS.iter().copied().unique().collect_vec());
        assert_eq!(ABI_PARAM_REGS.to_vec(), ABI_PARAM_REGS.iter().copied().unique().collect_vec());
        assert_eq!(ABI_CALL_VOLATILE_REGS.to_vec(), ABI_CALL_VOLATILE_REGS.iter().copied().unique().collect_vec());
        assert_eq!(ABI_CALL_NON_VOLATILE_REGS.to_vec(), ABI_CALL_NON_VOLATILE_REGS.iter().copied().unique().collect_vec());

        assert_eq!(Register::ALL.len(), ABI_CALL_VOLATILE_REGS.len() + ABI_CALL_NON_VOLATILE_REGS.len());
    }
}
