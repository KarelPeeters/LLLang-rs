use std::cmp::min;

use derive_more::Constructor;

use crate::mid::ir::{CastKind, InstructionInfo, Program, ProgramTypes, Signed, TypeInfo, Value};

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
    let mut stack = Stack::default();
    let all_bits = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();

    let (inner, depth) = extract_minimal_cast_chain_impl(prog, &mut stack, value, all_bits);

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

#[derive(Default)]
pub struct Stack {
    vec: Vec<CastOp>,
}

fn extract_minimal_cast_chain_impl(prog: &Program, stack: &mut Stack, value: Value, bits_used: u32) -> (Value, usize) {
    match value {
        Value::Instr(instr) => {
            match prog.get_instr(instr) {
                &InstructionInfo::Cast { ty, kind, value } => {
                    let full_before = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();
                    let full_after = prog.get_type(ty).unwrap_int().unwrap();

                    match kind {
                        CastKind::IntTruncate => assert!(full_after <= full_before),
                        CastKind::IntExtend(_) => assert!(full_after >= full_before),
                    }

                    let before = min(bits_used, full_before);
                    let after = min(bits_used, full_after);

                    if before != after {
                        stack.push(CastOp::new(kind, after));
                    };

                    let (inner, depth) = extract_minimal_cast_chain_impl(prog, stack, value, before);
                    return (inner, depth + 1);
                }
                _ => {}
            }
        }
        _ => {}
    }

    // we're returning, push the initial truncate we're still missing
    let bits = prog.get_type(prog.type_of_value(value)).unwrap_int().unwrap();
    if bits != bits_used {
        stack.push(CastOp::new(CastKind::IntTruncate, bits_used));
    }

    (value, 0)
}

/// Try combining the two cast operations into a single one.
///
/// The order of operations is `y = outer(inner(x))`.
///
/// This function makes the following assumptions:
///   * `inner` actually changed the number of bits
///   * `inner` has no more bits than `outer`
fn try_combine_cast_kinds(inner: CastOp, outer: CastOp) -> Option<CastOp> {
    assert!(inner.bits <= outer.bits);

    match (inner.kind, outer.kind) {
        // can't be fused
        (CastKind::IntTruncate, CastKind::IntExtend(_)) | (CastKind::IntExtend(_), CastKind::IntTruncate) => None,

        // trivially fusable, this will keep the smallest bit count
        (CastKind::IntTruncate, CastKind::IntTruncate) => Some(CastOp::new(CastKind::IntTruncate, inner.bits)),

        // sometimes fusable, if possible this will keep the largest bit count
        (CastKind::IntExtend(inner_signed), CastKind::IntExtend(outer_signed)) => {
            (match (inner_signed, outer_signed) {
                // trivially fusable, we're just continuing to extend in the same way
                (Signed::Signed, Signed::Signed) => Some(Signed::Signed),
                (Signed::Unsigned, Signed::Unsigned) => Some(Signed::Unsigned),

                // unsigned added at least one 0, which will be replicated by signed
                (Signed::Unsigned, Signed::Signed) => Some(Signed::Unsigned),

                // can't be fused, the result will be some sign bits followed by some zeros
                (Signed::Signed, Signed::Unsigned) => None,
            }).map(|signed| CastOp::new(CastKind::IntExtend(signed), outer.bits))
        }
    }
}

impl Stack {
    fn push(&mut self, mut inner: CastOp) {
        while let Some(outer) = self.vec.last() {
            assert!(inner.bits <= outer.bits);

            if let Some(combined) = try_combine_cast_kinds(inner, *outer) {
                inner = combined;
                self.vec.pop();
                continue;
            } else {
                break;
            }
        }

        self.vec.push(inner);
    }

    fn finish(self) -> Vec<CastOp> {
        let mut inner = self.vec;
        inner.reverse();
        inner
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
