//! Constant discovery uses shared class annotations. Contextual arithmetic
//! retains selected exact source premises when implicit provenance is requested.
use super::*;
use crate::kernel::Proposition;
use crate::kernel::PureFactContext;
use crate::kernel::assumptions::record_implicit_reasoning_provenance;
use std::collections::{BTreeMap, BTreeSet};
impl EqualityGraph {
    pub(in crate::kernel) fn wide_constant(
        &self,
        context: &PureFactContext,
        term: &Bitvector32Term,
    ) -> Option<u64> {
        fn evaluate(
            context: &PureFactContext,
            term: &Bitvector32Term,
            active: &mut BTreeSet<usize>,
            memo: &mut BTreeMap<usize, Option<u64>>,
        ) -> Option<u64> {
            if !crate::kernel::assumptions::implicit_reasoning_provenance_capturing()
                && let Some(value) = context.equality_graph.uint64_constant(term)
            {
                return Some(value);
            }
            // Identities live only for this query. No deep term clone or
            // structural comparison is needed for the traversal memo.
            let identity = term as *const Bitvector32Term as usize;
            if let Some(value) = memo.get(&identity) {
                return *value;
            }
            // Equality cycles and deeply nested arithmetic are search, not
            // permission to grow the native stack without a bound.
            if active.len() >= 128 {
                return None;
            }
            if !active.insert(identity) {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            let mut value = match term {
                Bitvector32Term::UInt64Constant(value) => Some(*value),
                Bitvector32Term::Int64Constant(value) => Some(*value as u64),
                Bitvector32Term::Int64Add(left, right)
                | Bitvector32Term::Int64Subtract(left, right)
                | Bitvector32Term::Int64Multiply(left, right)
                | Bitvector32Term::Int64Divide(left, right)
                | Bitvector32Term::Int64Remainder(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .and_then(|(a, b)| {
                            let (a, b) = (a as i64, b as i64);
                            match term {
                                Bitvector32Term::Int64Add(..) => a.checked_add(b),
                                Bitvector32Term::Int64Subtract(..) => a.checked_sub(b),
                                Bitvector32Term::Int64Multiply(..) => a.checked_mul(b),
                                Bitvector32Term::Int64Divide(..) => a.checked_div(b),
                                _ => a.checked_rem(b),
                            }
                            .map(|value| value as u64)
                        })
                }
                Bitvector32Term::Int64From32(inner) | Bitvector32Term::Int64FromUInt32(inner) => {
                    context
                        .known_signed_constant_after_normalization(inner)
                        .map(|a| {
                            if matches!(term, Bitvector32Term::Int64From32(..)) {
                                a as i32 as i64 as u64
                            } else {
                                u64::from(a as u32)
                            }
                        })
                }
                Bitvector32Term::UInt64Add(left, right) => evaluate(context, left, active, memo)
                    .zip(evaluate(context, right, active, memo))
                    .map(|(a, b)| a.wrapping_add(b)),
                Bitvector32Term::UInt64Subtract(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| a.wrapping_sub(b))
                }
                Bitvector32Term::UInt64Multiply(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| a.wrapping_mul(b))
                }
                Bitvector32Term::UInt64Divide(left, right)
                | Bitvector32Term::UInt64Remainder(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .and_then(|(a, b)| {
                            if b == 0 {
                                return None;
                            }
                            Some(if matches!(term, Bitvector32Term::UInt64Divide(..)) {
                                a / b
                            } else {
                                a % b
                            })
                        })
                }
                Bitvector32Term::UInt64BitwiseAnd(left, right)
                | Bitvector32Term::UInt64BitwiseOr(left, right)
                | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                    evaluate(context, left, active, memo)
                        .zip(evaluate(context, right, active, memo))
                        .map(|(a, b)| match term {
                            Bitvector32Term::UInt64BitwiseAnd(..) => a & b,
                            Bitvector32Term::UInt64BitwiseOr(..) => a | b,
                            _ => a ^ b,
                        })
                }
                Bitvector32Term::UInt64BitwiseNot(inner) => {
                    evaluate(context, inner, active, memo).map(|a| !a)
                }
                Bitvector32Term::UInt64ShiftLeft(left, right)
                | Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
                    let count = context
                        .known_signed_constant_after_normalization(right)
                        .map(|a| u64::from(a as u32))
                        .or_else(|| evaluate(context, right, active, memo));
                    evaluate(context, left, active, memo)
                        .zip(count)
                        .and_then(|(a, b)| {
                            if b >= 64 {
                                return None;
                            }
                            Some(if matches!(term, Bitvector32Term::UInt64ShiftLeft(..)) {
                                a.wrapping_shl(b as u32)
                            } else {
                                a >> b
                            })
                        })
                }
                Bitvector32Term::UInt64From32(inner) | Bitvector32Term::UInt64FromInt32(inner) => {
                    context
                        .known_signed_constant_after_normalization(inner)
                        .map(|a| {
                            if matches!(term, Bitvector32Term::UInt64FromInt32(..)) {
                                a as i32 as i64 as u64
                            } else {
                                u64::from(a as u32)
                            }
                        })
                }
                Bitvector32Term::UInt64FromInt64(inner) => evaluate(context, inner, active, memo),
                Bitvector32Term::UInt32From64(inner) => {
                    evaluate(context, inner, active, memo).map(|a| u64::from(a as u32))
                }
                _ => None,
            };
            if value.is_none()
                && let Some(neighbors) = context
                    .equality_graph
                    .admitted
                    .bitvector64_equality_facts
                    .get(term)
            {
                for (equal, fact) in neighbors.iter() {
                    value = evaluate(context, equal, active, memo);
                    if value.is_some() {
                        record_implicit_reasoning_provenance(
                            context,
                            &Proposition::ConditionIs(fact.clone(), true),
                        );
                        break;
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
