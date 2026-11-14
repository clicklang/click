//! Rule C: σ of a 32-bit quotient or remainder is the quotient or remainder
//! at the other signedness of σ of its operands, on nonnegative operands.
//!
//! σ, the 32-bit sign cast, is a node of its own ("Every format its own
//! nodes", step 4b). For a dividend `A` and a divisor `B` read at one
//! signedness, with `0 <= A < 2^31` and `0 < B < 2^31`, both readings of
//! each operand are the same number, and truncating and unsigned division
//! agree on it, as do the remainders; the result lies in `[0, A]`, which
//! both formats hold, so σ of it is the same number too:
//!
//! - `(a / b) as int32 == (a as int32) / (b as int32)` for `uint32` `a`,
//!   `b` whose `int32` readings are `0 <= a as int32` and `0 < b as int32`;
//! - `(x / y) as uint32 == (x as uint32) / (y as uint32)` for `int32` `x`,
//!   `y` with `0 <= x` and `0 < y`;
//!
//! and the same for `%`. The divisor must be positive, not only
//! nonnegative: a quotient by zero is not folded, and its value is not
//! related across the two signednesses.
//!
//! [`PureFactContext::decide_by_sign_cast_division`] answers a 32-bit
//! comparison one of whose sides is σ of a quotient or remainder by
//! deciding the comparison with that side read at the other signedness:
//! a match on each side's root, two sign decisions per side, and one
//! decision of the rewritten comparison, with the rule off inside them, as
//! the sign-bit rule is (`sign_bit.rs`). Assuming such a comparison also
//! files its reading, as the sign-bit rule files its equivalent. No other
//! fact is visited.

use super::*;
use crate::kernel::MachineBinaryOp as Op;
use crate::kernel::MachineCastSpelling;
use crate::kernel::MachineIntegerType as Ty;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{
        ComparisonOperand, NativeComparisonView, comparison_view, condition_for_operand_views,
        structural_native_comparison_view,
    },
};
use crate::kernel::{MachineOperandView as View, SharedMachineIntegerTerm};

thread_local! {
    static DECIDING_SIGN_CAST_DIVISION: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

/// Marks a rule-C decision in progress, so the decisions it makes do not
/// apply the rule again.
struct Deciding(bool);

impl Deciding {
    fn enter() -> Self {
        Self(DECIDING_SIGN_CAST_DIVISION.with(|deciding| deciding.replace(true)))
    }
}

impl Drop for Deciding {
    fn drop(&mut self) {
        DECIDING_SIGN_CAST_DIVISION.with(|deciding| deciding.set(self.0));
    }
}

/// The other 32-bit signedness.
fn other(format: Ty) -> Ty {
    if format == Ty::Int32 {
        Ty::UInt32
    } else {
        Ty::Int32
    }
}

/// `left op right` at the 32-bit `format`, by its folding constructor.
fn division_at(format: Ty, op: Op, left: MachineTerm, right: MachineTerm) -> MachineTerm {
    match (format, op) {
        (Ty::Int32, Op::Divide) => MachineTerm::divide(left, right),
        (Ty::Int32, _) => MachineTerm::remainder(left, right),
        (_, Op::Divide) => MachineTerm::unsigned_divide(left, right),
        (_, _) => MachineTerm::unsigned_remainder(left, right),
    }
}

fn comparison(condition: &ConditionTerm) -> Option<NativeComparisonView<'_>> {
    let view = if matches!(condition, ConditionTerm::Compare { .. }) {
        comparison_view(condition, true)?
    } else {
        structural_native_comparison_view(condition, true)?
    };
    matches!(view.format, Ty::Int32 | Ty::UInt32).then_some(view)
}

fn division_operands(term: View<'_>) -> Option<(Ty, Op, [View<'_>; 2])> {
    let (MachineCastSpelling::Generic, source, destination, operand) = term.cast()? else {
        return None;
    };
    if !crate::kernel::is_sign_cast32(source, destination) {
        return None;
    }
    let (format, op, operands) = operand.binary()?;
    (format == source && matches!(op, Op::Divide | Op::Remainder)).then_some((source, op, operands))
}

fn cast_operand(source: Ty, destination: Ty, value: View<'_>) -> ComparisonOperand<'static> {
    match value {
        View::Legacy(value) => ComparisonOperand::Constant(MachineTerm::sign_cast32(
            source,
            destination,
            value.clone(),
        )),
        View::Shared(_) => {
            ComparisonOperand::Observation(value.retain(source).checking_cast_operand(destination))
        }
    }
}

fn division_at_views(format: Ty, op: Op, operands: [View<'_>; 2]) -> ComparisonOperand<'static> {
    use crate::kernel::{KernelTerm, KernelTermImport};
    if let [View::Legacy(left), View::Legacy(right)] = operands {
        return ComparisonOperand::Constant(division_at(format, op, left.clone(), right.clone()));
    }
    let literal = |operand: View<'_>| {
        operand
            .literal()
            .map(|term| MachineTerm::operand32(format, term))
    };
    if let [Some(left), Some(right)] = operands.map(literal) {
        return ComparisonOperand::Constant(division_at(format, op, left, right));
    }
    if op == Op::Divide && literal(operands[1]).is_some_and(|term| term.constant32() == Some(1)) {
        return match literal(operands[0]) {
            Some(term) => ComparisonOperand::Constant(term),
            None => ComparisonOperand::Observation(operands[0].retain(format)),
        };
    }
    let roots = operands.map(|operand| {
        if let Some(literal) = literal(operand) {
            KernelTermImport::default()
                .machine_arithmetic(format, &literal)
                .expect("typed literal")
        } else {
            let View::Shared(root) = operand else {
                unreachable!("shared cast operands")
            };
            root.with_machine_observation_type(format)
        }
    });
    ComparisonOperand::Observation(
        SharedMachineIntegerTerm::from_shared(
            format,
            KernelTerm::machine_binary_shared(format, op, roots),
        )
        .expect("shared division operands"),
    )
}

impl ConditionTerm {
    /// Whether this is a 32-bit comparison with a side that is σ of a
    /// quotient or remainder, which rule C reads. One match on the root and
    /// each side.
    pub(crate) fn names_sign_cast_division(&self) -> bool {
        comparison(self).is_some_and(|view| {
            view.operands
                .iter()
                .any(|operand| division_operands(operand.operand_view()).is_some())
        })
    }
}

impl PureFactContext {
    /// Rule C (module docs): `condition` decided with each side that is σ
    /// of a quotient or remainder read at the other signedness, when its
    /// operands are known nonnegative and its divisor positive. `None` when
    /// no side is one, an operand's sign is not decided, or the rewritten
    /// comparison is undecided.
    pub(super) fn decide_by_sign_cast_division(&self, condition: &ConditionTerm) -> Option<bool> {
        let rewritten = self.sign_cast_division_equivalent(condition)?;
        let _deciding = Deciding::enter();
        self.decide(&rewritten)
    }

    /// `condition` with each side that is σ of a quotient or remainder read
    /// at the other signedness (rule C), when this context decides its
    /// operands' signs; `None` when no side is read. Assuming a condition
    /// also files this reading, as the sign-bit rule files its equivalent,
    /// so a fact and its reading meet in every index.
    pub(in crate::kernel::assumptions) fn sign_cast_division_equivalent(
        &self,
        condition: &ConditionTerm,
    ) -> Option<ConditionTerm> {
        if DECIDING_SIGN_CAST_DIVISION.with(std::cell::Cell::get) {
            return None;
        }
        let mut view = comparison(condition)?;
        // Keep native written directions, including greater-than spellings.
        let relation = match condition {
            ConditionTerm::Compare {
                relation: CompareRelation::GreaterThan,
                ..
            }
            | ConditionTerm::IntegerGreaterThan(..) => {
                view.operands.swap(0, 1);
                CompareRelation::GreaterThan
            }
            ConditionTerm::Compare {
                relation: CompareRelation::GreaterEqual,
                ..
            }
            | ConditionTerm::IntegerGreaterEqual(..) => {
                view.operands.swap(0, 1);
                CompareRelation::GreaterEqual
            }
            _ => match view.relation {
                Relation::Equal | Relation::NotEqual => CompareRelation::Equal,
                Relation::Less => CompareRelation::LessThan,
                Relation::LessEqual => CompareRelation::LessEqual,
            },
        };
        let operands = view
            .operands
            .each_ref()
            .map(ComparisonOperand::operand_view);
        if !operands
            .iter()
            .any(|operand| division_operands(*operand).is_some())
        {
            return None;
        }
        let _deciding = Deciding::enter();
        let [left, right] = operands.map(|operand| self.sign_cast_division_reading(operand));
        if left.is_none() && right.is_none() {
            return None;
        }
        let retain = |operand| match operand {
            View::Legacy(term) => ComparisonOperand::Constant(term.clone()),
            View::Shared(_) => ComparisonOperand::Observation(operand.retain(view.format)),
        };
        let results = [
            left.unwrap_or_else(|| retain(operands[0])),
            right.unwrap_or_else(|| retain(operands[1])),
        ];
        let operands = results.each_ref().map(ComparisonOperand::operand_view);
        if view.relation == Relation::NotEqual {
            return Some(ConditionTerm::integer_not_equal(
                operands[0].observe(view.format)?,
                operands[1].observe(view.format)?,
            ));
        }
        Some(condition_for_operand_views(view.format, relation, operands))
    }

    /// σ of a quotient or remainder `term` read at the other signedness:
    /// the operator there over σ of its operands, when this context decides
    /// the dividend's `int32` reading nonnegative and the divisor's
    /// positive. `None` otherwise.
    fn sign_cast_division_reading(&self, term: View<'_>) -> Option<ComparisonOperand<'static>> {
        let (source, op, operands) = division_operands(term)?;
        let destination = other(source);
        let casted = operands.map(|operand| cast_operand(source, destination, operand));
        let signed = if source == Ty::Int32 {
            operands
        } else {
            casted.each_ref().map(ComparisonOperand::operand_view)
        };
        let zero = MachineTerm::constant(0);
        if self.decide(&condition_for_operand_views(
            Ty::Int32,
            CompareRelation::LessEqual,
            [View::Legacy(&zero), signed[0]],
        )) != Some(true)
            || self.decide(&condition_for_operand_views(
                Ty::Int32,
                CompareRelation::LessThan,
                [View::Legacy(&zero), signed[1]],
            )) != Some(true)
        {
            return None;
        }
        Some(division_at_views(
            destination,
            op,
            casted.each_ref().map(ComparisonOperand::operand_view),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;

    fn var(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    fn sigma(source: Ty, value: MachineTerm) -> MachineTerm {
        MachineTerm::sign_cast32(source, other(source), value)
    }

    fn signed_nonnegative(value: MachineTerm) -> ConditionTerm {
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), value)
    }

    fn signed_positive(value: MachineTerm) -> ConditionTerm {
        ConditionTerm::signed_less_than(MachineTerm::constant(0), value)
    }

    #[test]
    fn shared_sign_division_readings_preserve_guards_directions_and_sources() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        let shape = |condition: ConditionTerm| {
            let view = comparison(&condition).expect("machine comparison");
            (
                view.format,
                view.relation,
                view.operands
                    .each_ref()
                    .map(|operand| operand.operand_view().retain(view.format).value().clone()),
            )
        };
        for source in [Ty::Int32, Ty::UInt32] {
            for op in [Op::Divide, Op::Remainder] {
                let n = MachineTerm::add(var(189101), var(189102));
                let d = var(189103);
                let signed_n = if source == Ty::Int32 {
                    n.clone()
                } else {
                    sigma(source, n.clone())
                };
                let signed_d = if source == Ty::Int32 {
                    d.clone()
                } else {
                    sigma(source, d.clone())
                };
                for (nonnegative, positive) in [(true, true), (false, true), (true, false)] {
                    let sources = [
                        Proposition::ConditionIs(signed_nonnegative(signed_n.clone()), nonnegative),
                        Proposition::ConditionIs(signed_positive(signed_d.clone()), positive),
                    ];
                    let context = PureFactContext::new()
                        .assume_proposition(sources[0].clone())
                        .assume_proposition(sources[1].clone());
                    let left = sigma(source, division_at(source, op, n.clone(), d.clone()));
                    let right = var(189104);
                    let format = other(source);
                    for relation in [
                        CompareRelation::Equal,
                        CompareRelation::LessThan,
                        CompareRelation::LessEqual,
                        CompareRelation::GreaterThan,
                        CompareRelation::GreaterEqual,
                    ] {
                        let native = ConditionTerm::machine_compare(
                            format,
                            relation,
                            left.clone(),
                            right.clone(),
                        );
                        let (expected, native_used) = collect_reasoning_provenance(|| {
                            capture_implicit_reasoning_provenance(|| {
                                context.sign_cast_division_equivalent(&native).map(&shape)
                            })
                        });
                        let [left, right] = [&left, &right].map(|term| {
                            KernelTermImport::default()
                                .machine_arithmetic(format, term)
                                .unwrap()
                        });
                        let shared = condition_for_operand_views(
                            format,
                            relation,
                            [View::Shared(&left), View::Shared(&right)],
                        );
                        assert!(shared.names_sign_cast_division());
                        let exports = KernelTermExport::machine_export_count();
                        let (actual, used) = collect_reasoning_provenance(|| {
                            capture_implicit_reasoning_provenance(|| {
                                context.sign_cast_division_equivalent(&shared)
                            })
                        });
                        assert_eq!(KernelTermExport::machine_export_count(), exports);
                        assert_eq!(actual.map(&shape), expected, "{native:?}");
                        if nonnegative && positive {
                            assert!(
                                native_used.iter().all(|source| used.contains(source))
                                    && used
                                        .iter()
                                        .all(|source| context.contains_assumed_exact(source)),
                                "native={native_used:?}, shared={used:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn fresh_shared_sign_division_uses_structural_mask_bounds_without_export() {
        use crate::kernel::{
            KernelTerm, KernelTermExport, KernelTermImport, KernelType,
            MachineCastSpelling as Encoding, ProgramType,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let x = KernelTerm::variable(KernelType::C(ProgramType::UInt32), Variable(189113));
        let prefix = KernelTerm::machine_binary_shared(Ty::UInt32, Op::Add, [x.clone(), x]);
        let literal = |format, value| {
            KernelTermImport::default()
                .machine_arithmetic(format, &MachineTerm::constant_at32(format, value))
                .unwrap()
        };
        let n = KernelTerm::machine_binary_shared(
            Ty::UInt32,
            Op::BitwiseAnd,
            [prefix, literal(Ty::UInt32, 255)],
        );
        let q = KernelTerm::machine_binary_shared(
            Ty::UInt32,
            Op::Divide,
            [n.clone(), literal(Ty::UInt32, 2)],
        );
        let left = KernelTerm::machine_cast_shared(Encoding::Generic, Ty::UInt32, Ty::Int32, q);
        let cast_n = KernelTerm::machine_cast_shared(Encoding::Generic, Ty::UInt32, Ty::Int32, n);
        let right = KernelTerm::machine_binary_shared(
            Ty::Int32,
            Op::Divide,
            [cast_n, literal(Ty::Int32, 2)],
        );
        let query = ConditionTerm::integer_not_equal(
            View::Shared(&left).observe(Ty::Int32).unwrap(),
            View::Shared(&right).observe(Ty::Int32).unwrap(),
        );
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            PureFactContext::new().decide_by_sign_cast_division(&query),
            Some(false)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_sign_division_disequality_keeps_its_polarity() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        let (n, d) = (var(189115), var(189116));
        let context = PureFactContext::new()
            .assume_condition(signed_nonnegative(sigma(Ty::UInt32, n.clone())), true)
            .assume_condition(signed_positive(sigma(Ty::UInt32, d.clone())), true);
        let left = sigma(
            Ty::UInt32,
            division_at(Ty::UInt32, Op::Divide, n.clone(), d.clone()),
        );
        let right = division_at(
            Ty::Int32,
            Op::Divide,
            sigma(Ty::UInt32, n),
            sigma(Ty::UInt32, d),
        );
        let roots = [&left, &right].map(|term| {
            KernelTermImport::default()
                .machine_arithmetic(Ty::Int32, term)
                .unwrap()
        });
        let observed = roots
            .each_ref()
            .map(|root| View::Shared(root).observe(Ty::Int32).unwrap());
        let [left, right] = observed;
        let query = ConditionTerm::integer_not_equal(left, right);
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(context.decide_by_sign_cast_division(&query), Some(false));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_division_constructors_keep_literal_folding_and_format() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        let _session = crate::kernel::VerificationSession::enter();
        for format in [Ty::Int32, Ty::UInt32] {
            for op in [Op::Divide, Op::Remainder] {
                for (left, right) in [
                    (var(189111), MachineTerm::constant(1)),
                    (MachineTerm::constant(7), MachineTerm::uint32_constant(2)),
                    (MachineTerm::constant(7), MachineTerm::constant(0)),
                    (var(189111), var(189112)),
                    (
                        MachineTerm::Binary {
                            format,
                            op: Op::Add,
                            left: Box::new(MachineTerm::constant(1)),
                            right: Box::new(MachineTerm::constant(1)),
                        },
                        MachineTerm::constant(2),
                    ),
                    (
                        var(189111),
                        MachineTerm::Binary {
                            format,
                            op: Op::Add,
                            left: Box::new(MachineTerm::constant(0)),
                            right: Box::new(MachineTerm::constant(1)),
                        },
                    ),
                ] {
                    let expected = division_at(format, op, left.clone(), right.clone());
                    let roots = [&left, &right].map(|value| {
                        KernelTermImport::default()
                            .machine_arithmetic(format, value)
                            .unwrap()
                    });
                    let exports = KernelTermExport::machine_export_count();
                    let actual = division_at_views(format, op, roots.each_ref().map(View::Shared));
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    assert_eq!(*actual.operand_view().retain(format).value(), expected);
                }
            }
        }
    }

    /// A bound on σ(x) is a bound on `x`'s bits: `0 < d as int32` excludes
    /// `d == 0u32` (the difference graph's σ link, rule K6's identity).
    #[test]
    fn a_bound_on_a_sign_cast_bounds_its_operand() {
        let d = var(189_001);
        let context = PureFactContext::new()
            .assume_condition(signed_positive(sigma(Ty::UInt32, d.clone())), true);
        assert_eq!(
            context.decide(&ConditionTerm::uint32_equal(
                d.clone(),
                MachineTerm::uint32_constant(0)
            )),
            Some(false)
        );
        assert_eq!(
            context.decide(&ConditionTerm::unsigned_less_equal(
                d,
                MachineTerm::uint32_constant(i32::MAX as u32)
            )),
            Some(true)
        );
    }

    /// Rule C in both directions, for `/` and `%`: σ of the quotient is the
    /// quotient at the other signedness of σ of the operands, on a
    /// nonnegative dividend and a positive divisor.
    #[test]
    fn a_sign_cast_quotient_is_the_other_quotient_on_nonnegative_operands() {
        for op in [Op::Divide, Op::Remainder] {
            for source in [Ty::UInt32, Ty::Int32] {
                let (n, d) = (var(189_010), var(189_011));
                let (signed_n, signed_d) = if source == Ty::Int32 {
                    (n.clone(), d.clone())
                } else {
                    (sigma(source, n.clone()), sigma(source, d.clone()))
                };
                let context = PureFactContext::new()
                    .assume_condition(signed_nonnegative(signed_n), true)
                    .assume_condition(signed_positive(signed_d), true);
                let cast = sigma(source, division_at(source, op, n.clone(), d.clone()));
                let other_quotient = division_at(
                    other(source),
                    op,
                    sigma(source, n.clone()),
                    sigma(source, d.clone()),
                );
                let equality = ConditionTerm::machine_compare(
                    other(source),
                    crate::kernel::CompareRelation::Equal,
                    cast,
                    other_quotient,
                );
                assert_eq!(
                    context.decide_by_sign_cast_division(&equality),
                    Some(true),
                    "{op:?} from {source:?}"
                );
            }
        }
    }

    /// Rule C needs the dividend known nonnegative: `u32::MAX / 2` is not
    /// `-1 / 2`.
    #[test]
    fn a_sign_cast_quotient_with_a_dividend_of_unknown_sign_is_not_read() {
        let (n, d) = (var(189_020), var(189_021));
        let context = PureFactContext::new()
            .assume_condition(signed_positive(sigma(Ty::UInt32, d.clone())), true);
        let equality = ConditionTerm::equal(
            sigma(
                Ty::UInt32,
                MachineTerm::unsigned_divide(n.clone(), d.clone()),
            ),
            MachineTerm::divide(sigma(Ty::UInt32, n), sigma(Ty::UInt32, d)),
        );
        assert_eq!(context.decide_by_sign_cast_division(&equality), None);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!(
        "../../../scaling_tests/kernel/assumptions/condition_reasoning/sign_cast_division/tests.rs"
    );
}
