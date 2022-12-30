use std::cmp::min;

use derive_more::Constructor;

use crate::mid::ir::{CastKind, InstructionInfo, Program, ProgramTypes, Scoped, Signed, TypeInfo, Value};

#[derive(Debug, Copy, Clone, Constructor, Eq, PartialEq)]
pub struct CastOp {
    pub kind: CastKind,
    pub bits: u32,
}

#[derive(Debug)]
pub struct CastChain {
    pub ops: Vec<CastOp>,
    pub inner: Value,
    pub origin_cast_count: usize,
}

/// Get an optimized version of the cast operations to apply.
// TODO it appears the longest possible optimized chain has 3 operations in it:
//   * truncate, extend(signed), extend(unsigned)
//   can we rewrite this entire thing to make use of this fact, and end up with something a lot simpler and faster?
pub fn extract_minimal_cast_chain(prog: &Program, value: Value) -> CastChain {
    let (stack, inner, depth) = extract_minimal_cast_chain_impl(prog, value);

    CastChain {
        ops: stack.finish(),
        inner,
        origin_cast_count: depth,
    }
}

impl CastOp {
    pub fn to_instruction(self, types: &mut ProgramTypes, input: Value) -> InstructionInfo {
        let CastOp { kind, bits } = self;

        InstructionInfo::Cast {
            ty: types.push(TypeInfo::Integer { bits }),
            kind,
            value: input,
        }
    }
}

/// A representation of the final stack operation.
///
/// `inner_real` is the size of the innermost input value.
/// The other fields should be interpreted as sequential operations:
/// * truncate to `real` bits
/// * sign extend to `signed`  bits
/// * zero extend to `unsigned` bits
///
/// For these operations to be valid, the following conditions must hold:
/// * `real <= inner_real`
/// * `real <= signed <= unsigned`.
#[derive(Debug)]
pub struct Stack {
    inner_real: u32,
    real: u32,
    signed: u32,
    unsigned: u32,
}

fn extract_minimal_cast_chain_impl(prog: &Program, value: Value) -> (Stack, Value, usize) {
    if let Value::Scoped(Scoped::Instr(instr)) = value {
        if let &InstructionInfo::Cast { ty, kind, value: next } = prog.get_instr(instr) {
            let (mut stack, inner, depth) = extract_minimal_cast_chain_impl(prog, next);
            let bits = prog.get_type(ty).unwrap_int().unwrap();
            stack.cast(CastOp::new(kind, bits));
            return (stack, inner, depth + 1);
        }
    }

    let bits = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();
    (Stack::new(bits), value, 0)
}

impl Stack {
    fn new(real: u32) -> Self {
        Stack {
            inner_real: real,
            real,
            signed: real,
            unsigned: real,
        }
    }

    fn cast(&mut self, next: CastOp) {
        let CastOp { kind, bits } = next;

        match kind {
            CastKind::IntTruncate => {
                assert!(bits <= self.unsigned);
                self.real = min(self.real, bits);
                self.signed = min(self.signed, bits);
                self.unsigned = min(self.unsigned, bits);
            }
            CastKind::IntExtend(signed) => {
                assert!(bits >= self.unsigned);
                match signed {
                    Signed::Signed => {
                        if self.signed == self.unsigned {
                            self.signed = bits;
                        }
                        self.unsigned = bits;
                    }
                    Signed::Unsigned => {
                        self.unsigned = bits;
                    }
                }
            }
        }

        assert!(self.real <= self.inner_real && self.real <= self.signed && self.signed <= self.unsigned);
    }

    fn finish(self) -> Vec<CastOp> {
        let Stack { inner_real, real, signed, unsigned } = self;
        let mut result = vec![];

        if real != inner_real {
            result.push(CastOp::new(CastKind::IntTruncate, real));
        }
        if signed != real {
            result.push(CastOp::new(CastKind::IntExtend(Signed::Signed), signed));
        }
        if unsigned != signed {
            result.push(CastOp::new(CastKind::IntExtend(Signed::Unsigned), unsigned));
        }

        result
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;

    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;

    use crate::mid::ir::{CastKind, InstructionInfo, ParameterInfo, Program, Signed, Value};
    use crate::mid::util::cast_chain::{CastOp, extract_minimal_cast_chain};

    fn build_chain(start_bits: u32, steps: &[CastOp]) -> (Program, Value, Value) {
        let mut prog = Program::default();

        let start_ty = prog.define_type_int(start_bits);
        let start = prog.define_param(ParameterInfo { ty: start_ty }).into();

        let mut curr: Value = start;

        for &CastOp { kind, bits } in steps {
            let ty = prog.define_type_int(bits);
            curr = prog.define_instr(InstructionInfo::Cast {
                ty,
                kind,
                value: curr,
            }).into();
        }

        (prog, start, curr)
    }

    fn optimize_chain(start_bits: u32, steps: &[CastOp]) -> Vec<CastOp> {
        let (prog, start, value) = build_chain(start_bits, steps);

        let chain = extract_minimal_cast_chain(&prog, value);
        assert_eq!(chain.inner, start);
        assert_eq!(chain.origin_cast_count, steps.len());

        println!("Original steps:");
        println!("  start with {} bits", start_bits);
        for &CastOp { kind, bits } in steps {
            println!("  {:?} -> {} bits", kind, bits);
        }

        println!();

        println!("Extracted steps:");
        for &CastOp { kind, bits } in &chain.ops {
            println!("  {:?} -> {} bits", kind, bits);
        }

        chain.ops
    }

    fn gen_random_chain(start_bits: u32, len: usize, rng: &mut impl Rng) -> Vec<CastOp> {
        let mut steps = vec![];
        let mut curr_bits = start_bits;

        for _ in 0..len {
            let bits = rng.gen_range(0..64);

            let extend = match bits.cmp(&curr_bits) {
                Ordering::Less => false,
                Ordering::Equal => rng.gen(),
                Ordering::Greater => true,
            };

            let kind = if extend {
                CastKind::IntExtend([Signed::Signed, Signed::Unsigned][rng.gen_range(0..2)])
            } else {
                CastKind::IntTruncate
            };

            steps.push(CastOp::new(kind, bits));
            curr_bits = bits;
        }

        steps
    }

    fn assert_expected(start_bits: u32, before: &[CastOp], expected: &[CastOp]) {
        let result = optimize_chain(start_bits, before);
        assert_eq!(&result, expected);
    }

    #[test]
    fn truncate() {
        assert_expected(16, &[
            CastOp::new(CastKind::IntTruncate, 8),
        ], &[
            CastOp::new(CastKind::IntTruncate, 8),
        ])
    }

    #[test]
    fn cutoff() {
        assert_expected(16, &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 64),
            CastOp::new(CastKind::IntTruncate, 32),
        ], &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 32),
        ])
    }

    #[test]
    fn cutout() {
        assert_expected(16, &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 64),
            CastOp::new(CastKind::IntTruncate, 16),
        ], &[])
    }

    #[test]
    fn signed_signed() {
        assert_expected(32, &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 32),
            CastOp::new(CastKind::IntExtend(Signed::Signed), 64),
        ], &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 64),
        ]);
    }

    #[test]
    fn second_fuse_attempt() {
        assert_expected(16, &[
            CastOp::new(CastKind::IntExtend(Signed::Signed), 32),
            CastOp::new(CastKind::IntExtend(Signed::Unsigned), 64),
            CastOp::new(CastKind::IntTruncate, 1),
            CastOp::new(CastKind::IntExtend(Signed::Unsigned), 2),
            CastOp::new(CastKind::IntExtend(Signed::Signed), 3),
            CastOp::new(CastKind::IntExtend(Signed::Unsigned), 4),
            CastOp::new(CastKind::IntExtend(Signed::Signed), 5),
        ], &[
            CastOp::new(CastKind::IntTruncate, 1),
            CastOp::new(CastKind::IntExtend(Signed::Unsigned), 5),
        ]);
    }

    #[test]
    fn random_chains() {
        let mut rng = StdRng::seed_from_u64(0);

        let n = 10;
        for i in 0.. {
            println!("Generating chain {}/{}", i + 1, n);
            let start_bits = 32;
            let steps = gen_random_chain(start_bits, 128, &mut rng);
            let result = optimize_chain(start_bits, &steps);

            if result.len() >= 3 {
                break;
            }

            println!();
            println!();
        }
    }
}
