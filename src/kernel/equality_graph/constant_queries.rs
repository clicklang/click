//! Constant discovery uses shared class annotations. Contextual arithmetic
//! retains selected exact source premises when implicit provenance is requested.
use super::*;
use crate::kernel::assumptions::record_implicit_reasoning_provenance;
use crate::kernel::{
    KernelMachineCastEncoding as Cast, MachineOperandView as V, Proposition, PureFactContext,
};
use std::collections::{BTreeMap, BTreeSet};

impl EqualityGraph {
    pub(in crate::kernel) fn wide_constant(
        &self,
        context: &PureFactContext,
        term: &Bitvector32Term,
    ) -> Option<u64> {
        self.wide_constant_view(context, V::Legacy(term))
    }

    pub(in crate::kernel) fn wide_constant_view(
        &self,
        context: &PureFactContext,
        term: V<'_>,
    ) -> Option<u64> {
        fn evaluate(
            context: &PureFactContext,
            term: V<'_>,
            active: &mut BTreeSet<(bool, u64)>,
            memo: &mut BTreeMap<(bool, u64), Option<u64>>,
        ) -> Option<u64> {
            if !crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
                && let Some(value) = context.equality_graph.uint64_constant_view(term)
            {
                return Some(value);
            }
            let identity = match term {
                V::Legacy(term) => (false, term as *const Bitvector32Term as usize as u64),
                V::Shared(term) => (true, term.id()),
            };
            if let Some(value) = memo.get(&identity) {
                return *value;
            }
            // Preserve the existing contextual evaluator's bounded recursion.
            if active.len() >= 128 || !active.insert(identity) {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            let mut value = match term.literal() {
                Some(Bitvector32Term::UInt64Constant(value)) => Some(value),
                Some(Bitvector32Term::Int64Constant(value)) => Some(value as u64),
                _ => None,
            };
            if let Some((format, op, [left, right])) = term.binary()
                && (matches!(
                    format,
                    MachineIntegerType::Int64 | MachineIntegerType::UInt64
                ) && matches!(
                    op,
                    MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::Multiply
                        | MachineBinaryOp::Divide
                        | MachineBinaryOp::Remainder
                ) || format == MachineIntegerType::UInt64
                    && matches!(
                        op,
                        MachineBinaryOp::BitwiseAnd
                            | MachineBinaryOp::BitwiseOr
                            | MachineBinaryOp::BitwiseXor
                            | MachineBinaryOp::ShiftLeft
                            | MachineBinaryOp::ShiftRight
                    ))
            {
                use MachineBinaryOp as Op;
                let operands = if format == MachineIntegerType::UInt64
                    && matches!(op, Op::ShiftLeft | Op::ShiftRight)
                {
                    let count = context
                        .known_signed_constant_after_normalization_view(right)
                        .map(|a| u64::from(a as u32))
                        .or_else(|| evaluate(context, right, active, memo));
                    evaluate(context, left, active, memo).zip(count)
                } else {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                };
                value = operands.and_then(|(a, b)| {
                    if format == MachineIntegerType::Int64 {
                        let (a, b) = (a as i64, b as i64);
                        return match op {
                            Op::Add => a.checked_add(b),
                            Op::Subtract => a.checked_sub(b),
                            Op::Multiply => a.checked_mul(b),
                            Op::Divide => a.checked_div(b),
                            Op::Remainder => a.checked_rem(b),
                            _ => None,
                        }
                        .map(|value| value as u64);
                    }
                    if format != MachineIntegerType::UInt64 {
                        return None;
                    }
                    Some(match op {
                        Op::Add => a.wrapping_add(b),
                        Op::Subtract => a.wrapping_sub(b),
                        Op::Multiply => a.wrapping_mul(b),
                        Op::Divide if b != 0 => a / b,
                        Op::Remainder if b != 0 => a % b,
                        Op::BitwiseAnd => a & b,
                        Op::BitwiseOr => a | b,
                        Op::BitwiseXor => a ^ b,
                        Op::ShiftLeft if b < 64 => a.wrapping_shl(b as u32),
                        Op::ShiftRight if b < 64 => a >> b,
                        _ => return None,
                    })
                });
            } else if let Some((encoding, _, _, inner)) = term.cast() {
                value = match encoding {
                    Cast::Int64From32 | Cast::UInt64FromInt32 => context
                        .known_signed_constant_after_normalization_view(inner)
                        .map(|a| a as i32 as i64 as u64),
                    Cast::Int64FromUInt32 | Cast::UInt64From32 => context
                        .known_signed_constant_after_normalization_view(inner)
                        .map(|a| u64::from(a as u32)),
                    Cast::UInt64FromInt64 => evaluate(context, inner, active, memo),
                    Cast::UInt32From64 => {
                        evaluate(context, inner, active, memo).map(|a| u64::from(a as u32))
                    }
                    Cast::Generic => None,
                };
            } else if let Some((MachineIntegerType::UInt64, MachineUnaryOp::BitwiseNot, inner)) =
                term.unary()
            {
                value = evaluate(context, inner, active, memo).map(|a| !a);
            }
            if value.is_none() {
                match term {
                    V::Legacy(term) => {
                        if let Some(neighbors) = context
                            .equality_graph
                            .admitted
                            .bitvector64_equality_facts
                            .get(term)
                        {
                            for (equal, fact) in neighbors.iter() {
                                value = evaluate(context, V::Legacy(equal), active, memo);
                                if value.is_some() {
                                    record_implicit_reasoning_provenance(
                                        context,
                                        &Proposition::ConditionIs(fact.clone(), true),
                                    );
                                    break;
                                }
                            }
                        }
                    }
                    V::Shared(_) => {
                        for (equal, source) in context
                            .equality_graph
                            .admitted
                            .wide_constant_sources
                            .neighbors(term)
                        {
                            value = evaluate(context, equal, active, memo);
                            if value.is_some() {
                                record_implicit_reasoning_provenance(context, source);
                                break;
                            }
                        }
                    }
                }
            }
            active.remove(&identity);
            memo.insert(identity, value);
            value
        }
        evaluate(context, term, &mut BTreeSet::new(), &mut BTreeMap::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::assumptions::{
        capture_implicit_reasoning_provenance, collect_reasoning_provenance,
    };
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermImport, KernelType, SharedMachineIntegerTerm,
    };

    #[test]
    fn shared_wide_constants_keep_exact_sources_and_branch_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt64;
        let var = |id| KernelTerm::variable(KernelType::C(ty.c_type()), Variable(id));
        let root =
            KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [var(995871), var(995871)]);
        let operand = SharedMachineIntegerTerm::from_shared(ty, root.clone()).unwrap();
        let alias = SharedMachineIntegerTerm::from_shared(ty, var(995872)).unwrap();
        let source = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                IntegerTerm::Machine(operand.clone()),
                IntegerTerm::Machine(alias.clone()),
            ),
            true,
        );
        let literal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                IntegerTerm::Machine(alias),
                IntegerTerm::constant(7.into()),
            ),
            true,
        );
        let parent = PureFactContext::new().assume_proposition(source.clone());
        let child = parent.clone().assume_proposition(literal.clone());
        let query = SharedMachineIntegerTerm::from_shared(
            ty,
            KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]),
        )
        .unwrap();
        let read = |context: &PureFactContext| {
            capture_implicit_reasoning_provenance(|| {
                context.wide_constant_from_equalities_view(query.operand_view())
            })
        };
        assert_eq!(read(&parent), None);
        let (value, premises) = collect_reasoning_provenance(|| read(&child));
        assert_eq!(value, Some(14));
        assert!(premises.contains(&source));
        assert!(premises.contains(&literal));
        assert_eq!(read(&child.without_exact_fact(&literal)), None);
        assert_eq!(read(&parent), None);
        assert!(!query.has_boxed_operand());
        assert!(!operand.has_boxed_operand());
    }

    #[test]
    fn wide_source_index_keeps_a_written_endpoint_when_canonicalization_changes_it() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let written = Bitvector32Term::MachineIntegerCast {
            source: format,
            destination: format,
            value: Box::new(Bitvector32Term::Variable(Variable(995879))),
        };
        assert_ne!(crate::kernel::canonical_term(&written), written);
        let operand = SharedMachineIntegerTerm::from_shared(
            format,
            KernelTermImport::default()
                .machine_arithmetic(format, &written)
                .unwrap(),
        )
        .unwrap();
        let source = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(written),
                right: Box::new(Bitvector32Term::UInt64Constant(7)),
            },
            true,
        );
        let context = PureFactContext::new().assume_proposition(source.clone());
        let (value, sources) = collect_reasoning_provenance(|| {
            capture_implicit_reasoning_provenance(|| {
                context.wide_constant_from_equalities_view(operand.operand_view())
            })
        });
        assert_eq!(value, Some(7));
        assert!(sources.contains(&source));
        assert!(!operand.has_boxed_operand());
    }

    #[test]
    fn shared_wide_casts_preserve_sign_extension_and_low_words() {
        let _session = crate::kernel::VerificationSession::enter();
        use MachineIntegerType as Ty;
        for (ty, written, expected) in [
            (
                Ty::Int64,
                Bitvector32Term::Int64From32(Box::new(Bitvector32Term::Constant(u32::MAX))),
                u64::MAX,
            ),
            (
                Ty::UInt64,
                Bitvector32Term::UInt64FromInt32(Box::new(Bitvector32Term::Constant(u32::MAX))),
                u64::MAX,
            ),
            (
                Ty::Int64,
                Bitvector32Term::Int64FromUInt32(Box::new(Bitvector32Term::UInt32Constant(
                    u32::MAX,
                ))),
                u32::MAX as u64,
            ),
            (
                Ty::UInt64,
                Bitvector32Term::UInt64From32(Box::new(Bitvector32Term::UInt32Constant(u32::MAX))),
                u32::MAX as u64,
            ),
            (
                Ty::UInt64,
                Bitvector32Term::UInt64FromInt64(Box::new(Bitvector32Term::Int64Constant(-3))),
                (-3i64) as u64,
            ),
            (
                Ty::UInt32,
                Bitvector32Term::UInt32From64(Box::new(Bitvector32Term::UInt64Constant(
                    0x1234567887654321,
                ))),
                0x87654321,
            ),
        ] {
            let shared = SharedMachineIntegerTerm::from_shared(
                ty,
                KernelTermImport::default()
                    .machine_arithmetic(ty, &written)
                    .unwrap(),
            )
            .unwrap();
            let context = PureFactContext::new();
            assert_eq!(
                capture_implicit_reasoning_provenance(
                    || context.wide_constant_from_equalities_view(shared.operand_view())
                ),
                Some(expected)
            );
            assert_eq!(
                capture_implicit_reasoning_provenance(
                    || context.wide_constant_from_equalities(&written)
                ),
                Some(expected)
            );
            assert!(!shared.has_boxed_operand());
        }
    }

    #[test]
    fn shared_wide_constant_operations_preserve_partial_and_wrapping_results() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        use MachineBinaryOp as Op;
        use MachineIntegerType as Ty;
        for (ty, op, a, b, expected) in [
            (Ty::Int64, Op::Add, i64::MAX as u64, 1, None),
            (Ty::UInt64, Op::Add, u64::MAX, 1, Some(0)),
            (Ty::Int64, Op::Divide, i64::MIN as u64, u64::MAX, None),
            (Ty::UInt64, Op::Divide, 9, 0, None),
            (Ty::UInt64, Op::ShiftLeft, 1, 64, None),
            (Ty::UInt64, Op::ShiftLeft, 1, 63, Some(1 << 63)),
            (Ty::Int64, Op::Remainder, (-9i64) as u64, 4, Some(u64::MAX)),
            (Ty::UInt64, Op::BitwiseXor, 5, 3, Some(6)),
        ] {
            let literal = |value| {
                if ty == Ty::Int64 {
                    Bitvector32Term::Int64Constant(value as i64)
                } else {
                    Bitvector32Term::UInt64Constant(value)
                }
            };
            let written = Bitvector32Term::Binary {
                format: ty,
                op,
                left: Box::new(literal(a)),
                right: Box::new(literal(b)),
            };
            let shared = SharedMachineIntegerTerm::from_shared(
                ty,
                KernelTermImport::default()
                    .machine_arithmetic(ty, &written)
                    .unwrap(),
            )
            .unwrap();
            let actual = capture_implicit_reasoning_provenance(|| {
                context.wide_constant_from_equalities_view(shared.operand_view())
            });
            assert_eq!(actual, expected, "{ty:?} {op:?}");
            assert!(!shared.has_boxed_operand());
            assert_eq!(
                capture_implicit_reasoning_provenance(
                    || context.wide_constant_from_equalities(&written)
                ),
                expected
            );
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use crate::kernel::assumptions::{
        capture_implicit_reasoning_provenance, collect_reasoning_provenance,
    };
    use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm};
    include!("../../scaling_tests/kernel/equality_graph/constant_queries.rs");
}
