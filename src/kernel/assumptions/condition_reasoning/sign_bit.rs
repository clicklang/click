//! A signedness conversion's sign test is its operand's half-range test.
//!
//! Converting between the signed and unsigned formats of one width `N`
//! changes no bit, so the signed reading is negative exactly when the
//! unsigned reading exceeds the signed maximum `2^(N-1) - 1`:
//!
//! - `(intN)u < 0` holds exactly when `u > 2^(N-1) - 1`, for `u` unsigned,
//!   and `(intN)u >= 0` exactly when `u <= 2^(N-1) - 1`;
//! - `(uintN)x > 2^(N-1) - 1` holds exactly when `x < 0`, for `x` signed,
//!   and `(uintN)x <= 2^(N-1) - 1` exactly when `x >= 0`.
//!
//! At 32 bits the conversion is σ, a node of its own: the equivalent reads
//! the operand through σ, and reads σ of a σ the operand already is as that
//! σ's operand (a reading of the rule; the constructor keeps σ of σ as
//! written), so `u as int32 < 0` and `u > 2^31 - 1` are each other's
//! equivalents. At 64 bits a conversion reuses the word (a 64-bit
//! unsigned reading of a signed value wraps it in `UInt64FromInt64`). At 32
//! and 64 bits the rule holds for every word. At 8
//! and 16 bits the conversion is a generic `Cast` of a canonical
//! carrier, read in an `int32` comparison; the rule holds when the operand
//! lies in its own format's range, which the context must decide.
//!
//! [`PureFactContext::decide_by_sign_bit`] answers one such comparison by
//! deciding its equivalent, and a lookup of a known condition also looks up
//! its equivalent: one rewrite of the root and one decision or lookup, with
//! no visit of any other fact. An 8- or 16-bit sign test, or a 32-bit test
//! of σ, names a cast no plain comparison of its operand does, so assuming
//! one also files its operand's half-range test. The equivalent of the equivalent is the
//! original comparison, so the rule is not applied again inside it.

use super::*;
use crate::kernel::CompareRelation as R;
use crate::kernel::MachineIntegerType as Ty;
use crate::kernel::MachineTerm;
use crate::kernel::machine_integer::{
    Relation,
    comparison::{
        ComparisonOperand, NativeComparisonView, comparison_view, condition_for_operand_views,
        structural_native_comparison_view,
    },
};
use crate::kernel::{MachineCastSpelling as Encoding, MachineOperandView as View};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};

thread_local! {
    static DECIDING_SIGN_BIT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Marks a sign-bit decision in progress, so the decisions it makes do not
/// apply the rule again.
struct Deciding(bool);

impl Deciding {
    fn enter() -> Self {
        Self(DECIDING_SIGN_BIT.with(|deciding| deciding.replace(true)))
    }
}

impl Drop for Deciding {
    fn drop(&mut self) {
        DECIDING_SIGN_BIT.with(|deciding| deciding.set(self.0));
    }
}

/// The signed maximum `2^(N-1) - 1` of a width of 8, 16, 32 or 64 bits.
fn signed_maximum(bits: u32) -> i64 {
    i64::MAX >> (64 - bits)
}

fn comparison(condition: &ConditionTerm) -> Option<NativeComparisonView<'_>> {
    if matches!(condition, ConditionTerm::Compare { .. }) {
        comparison_view(condition, true)
    } else {
        structural_native_comparison_view(condition, true)
    }
}

fn retain(format: Ty, operand: View<'_>) -> ComparisonOperand<'static> {
    match operand {
        View::Legacy(value) => ComparisonOperand::Constant(value.clone()),
        View::Shared(_) => ComparisonOperand::Observation(operand.retain(format)),
    }
}

/// Read only a literal root, preserving the native rule's carrier convention.
fn constant(term: View<'_>) -> Option<i64> {
    match term.literal()? {
        bits32_constant!(value) => Some(i64::from(constant_u32(value))),
        int64_constant!(value) => Some(constant_i64(value)),
        uint64_constant!(value) => i64::try_from(constant_u64(value)).ok(),
        _ => None,
    }
}

/// The rule reads one inverse sign pair; it does not rewrite stored terms.
fn sign_cast(source: Ty, destination: Ty, operand: View<'_>) -> ComparisonOperand<'static> {
    if let Some(bits32_constant!(bits)) = operand.literal() {
        return ComparisonOperand::Constant(MachineTerm::constant_at32(
            destination,
            constant_u32(bits),
        ));
    }
    if let Some((Encoding::Generic, inner_source, inner_destination, value)) = operand.cast()
        && inner_source == destination
        && inner_destination == source
    {
        return retain(destination, value);
    }
    match operand {
        View::Legacy(value) => ComparisonOperand::Constant(MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(value.clone()),
            from: source,
            to: destination,
        }),
        View::Shared(_) => {
            ComparisonOperand::Observation(operand.retain(source).cast_operand(destination))
        }
    }
}

fn converted(source: Ty, destination: Ty, operand: View<'_>) -> ComparisonOperand<'static> {
    match operand {
        View::Legacy(value) => ComparisonOperand::Constant(MachineTerm::machine_integer_cast(
            source,
            destination,
            value.clone(),
        )),
        View::Shared(_) => ComparisonOperand::Observation(
            operand.retain(source).checking_cast_operand(destination),
        ),
    }
}

fn unsigned64_wrapper(operand: View<'_>) -> ComparisonOperand<'static> {
    match operand {
        View::Legacy(value) => ComparisonOperand::Constant(MachineTerm::legacy_cast(
            MachineCastSpelling::UInt64FromInt64,
            Box::new(value.clone()),
        )),
        View::Shared(root) => ComparisonOperand::Observation(
            crate::kernel::SharedMachineIntegerTerm::from_shared(
                Ty::UInt64,
                crate::kernel::KernelTerm::machine_cast_shared(
                    Encoding::UInt64FromInt64,
                    Ty::Int64,
                    Ty::UInt64,
                    root.with_machine_observation_type(Ty::Int64),
                ),
            )
            .expect("shared unsigned reading"),
        ),
    }
}

fn constant_on_the_right<'a>(view: &'a NativeComparisonView<'_>) -> Option<(R, View<'a>, i64)> {
    let relation = match view.relation {
        Relation::Equal => R::Equal,
        Relation::Less => R::LessThan,
        Relation::LessEqual => R::LessEqual,
        Relation::NotEqual => return None,
    };
    let [left, right] = view
        .operands
        .each_ref()
        .map(ComparisonOperand::operand_view);
    if let Some(value) = constant(right) {
        return Some((relation, left, value));
    }
    let value = constant(left)?;
    let mirrored = match relation {
        R::LessThan => R::GreaterThan,
        R::LessEqual => R::GreaterEqual,
        _ => return None,
    };
    Some((mirrored, right, value))
}

fn bound(format: Ty, relation: R, operand: View<'_>, value: i64) -> ConditionTerm {
    let value = match format {
        Ty::Int64 => MachineTerm::int64_constant(value),
        Ty::UInt64 => MachineTerm::uint64_constant(value as u64),
        _ => MachineTerm::constant(value as u32),
    };
    condition_for_operand_views(format, relation, [operand, View::Legacy(&value)])
}

fn sign_condition(format: Ty, operand: View<'_>, negative: bool) -> ConditionTerm {
    if negative {
        return bound(format, R::LessThan, operand, 0);
    }
    let zero = if format == Ty::Int64 {
        MachineTerm::int64_constant(0)
    } else {
        MachineTerm::constant(0)
    };
    condition_for_operand_views(format, R::LessEqual, [View::Legacy(&zero), operand])
}

/// A sign test `negative` (`< 0`, or `>= 0` when false) or a half-range
/// test `above` (`> max`, or `<= max` when false) of `term`: which one, and
/// its truth's polarity. `None` for any other comparison.
enum Test {
    Sign { negative: bool },
    Half { above: bool },
}

fn test(relation: R, value: i64, maximum: i64) -> Option<Test> {
    Some(match (relation, value) {
        (R::LessThan, 0) => Test::Sign { negative: true },
        (R::GreaterEqual, 0) => Test::Sign { negative: false },
        (R::LessEqual, -1) => Test::Sign { negative: true },
        (R::GreaterThan, -1) => Test::Sign { negative: false },
        (R::GreaterThan, value) if value == maximum => Test::Half { above: true },
        (R::LessEqual, value) if value == maximum => Test::Half { above: false },
        (R::GreaterEqual, value) if Some(value) == maximum.checked_add(1) => {
            Test::Half { above: true }
        }
        (R::LessThan, value) if Some(value) == maximum.checked_add(1) => {
            Test::Half { above: false }
        }
        _ => return None,
    })
}

impl PureFactContext {
    /// A signedness conversion's sign test, or its operand's half-range
    /// test, decided as the other (module docs). `None` when `condition` is
    /// neither, or its equivalent is undecided.
    pub(super) fn decide_by_sign_bit(&self, condition: &ConditionTerm) -> Option<bool> {
        if DECIDING_SIGN_BIT.with(std::cell::Cell::get) {
            return None;
        }
        // The range decisions and the equivalent's decision run with the
        // rule off: each is a comparison the rule would map back.
        let _deciding = Deciding::enter();
        self.sign_bit_equivalents(condition)?
            .into_iter()
            .find_map(|equivalent| self.decide(&equivalent))
    }

    /// The comparisons with the truth of `condition`, a signedness
    /// conversion's sign test or its operand's half-range test, or `None`.
    /// At most two: a 64-bit signed value's unsigned reading is its word or
    /// that word wrapped. One constant-size rewrite of the root, and for an
    /// 8- or 16-bit cast two range decisions about its operand.
    pub(in crate::kernel::assumptions) fn sign_bit_equivalent_conditions(
        &self,
        condition: &ConditionTerm,
    ) -> Vec<ConditionTerm> {
        if DECIDING_SIGN_BIT.with(std::cell::Cell::get) {
            return Vec::new();
        }
        let _deciding = Deciding::enter();
        self.sign_bit_equivalents(condition).unwrap_or_default()
    }

    /// `assume` run with the sign-bit rule off, so filing an equivalent
    /// does not file the original again.
    pub(in crate::kernel::assumptions) fn without_sign_bit_rule<T>(
        assume: impl FnOnce() -> T,
    ) -> T {
        let _deciding = Deciding::enter();
        assume()
    }

    fn sign_bit_equivalents(&self, condition: &ConditionTerm) -> Option<Vec<ConditionTerm>> {
        let view = comparison(condition)?;
        let widened = view.widened();
        let view = widened.as_ref().unwrap_or(&view);
        let (relation, operand, value) = constant_on_the_right(view)?;
        let format = view.format;
        let in_range = |term: View<'_>, lower: i64, upper: i64| {
            let lower = MachineTerm::constant(lower as u32);
            self.decide(&condition_for_operand_views(
                Ty::Int32,
                R::LessEqual,
                [View::Legacy(&lower), term],
            )) == Some(true)
                && self.decide(&bound(Ty::Int32, R::LessEqual, term, upper)) == Some(true)
        };
        // A narrow signedness conversion read through its int32 widening.
        if format == Ty::Int32
            && let Some((Encoding::Generic, widened_from, Ty::Int32, converted_operand)) =
                operand.cast()
            && let Some((Encoding::Generic, source, destination, inner)) = converted_operand.cast()
            && widened_from == destination
            && source.format().bits() == destination.format().bits()
            && source.format().bits() < 32
            && source.format().is_signed() != destination.format().is_signed()
        {
            let maximum = signed_maximum(source.format().bits());
            let inner = converted(source, Ty::Int32, inner);
            let inner = inner.operand_view();
            return Some(match test(relation, value, maximum)? {
                Test::Sign { negative } if destination.format().is_signed() => {
                    vec![bound(
                        Ty::Int32,
                        if negative {
                            R::GreaterThan
                        } else {
                            R::LessEqual
                        },
                        inner,
                        maximum,
                    )]
                }
                Test::Half { above } if !destination.format().is_signed() => {
                    vec![sign_condition(Ty::Int32, inner, above)]
                }
                _ => return None,
            });
        }
        // A narrow conversion of a 32-bit carrier needs its original range guards.
        if format == Ty::Int32
            && let Some((Encoding::Generic, source, destination, inner)) = operand.cast()
            && source.format().bits() == destination.format().bits()
            && source.format().bits() < 32
            && source.format().is_signed() != destination.format().is_signed()
        {
            let maximum = signed_maximum(source.format().bits());
            return Some(match test(relation, value, maximum)? {
                Test::Sign { negative } if destination.format().is_signed() => {
                    let unsigned_bound =
                        self.decide(&bound(Ty::UInt32, R::LessEqual, inner, 2 * maximum + 1))
                            == Some(true);
                    if !unsigned_bound && !in_range(inner, 0, 2 * maximum + 1) {
                        return None;
                    }
                    vec![bound(
                        Ty::Int32,
                        if negative {
                            R::GreaterThan
                        } else {
                            R::LessEqual
                        },
                        inner,
                        maximum,
                    )]
                }
                Test::Half { above } if !destination.format().is_signed() => {
                    if !in_range(inner, -maximum - 1, maximum) {
                        return None;
                    }
                    vec![sign_condition(Ty::Int32, inner, above)]
                }
                _ => return None,
            });
        }
        let wide = match format {
            Ty::Int32 | Ty::UInt32 => false,
            Ty::Int64 | Ty::UInt64 => true,
            _ => return None,
        };
        match (
            format.format().is_signed(),
            test(relation, value, signed_maximum(format.format().bits()))?,
        ) {
            (true, Test::Sign { negative }) => Some(if wide {
                let wrapped = unsigned64_wrapper(operand);
                [operand, wrapped.operand_view()]
                    .map(|word| {
                        bound(
                            Ty::UInt64,
                            if negative {
                                R::GreaterThan
                            } else {
                                R::LessEqual
                            },
                            word,
                            i64::MAX,
                        )
                    })
                    .to_vec()
            } else {
                let word = sign_cast(Ty::Int32, Ty::UInt32, operand);
                vec![bound(
                    Ty::UInt32,
                    if negative {
                        R::GreaterThan
                    } else {
                        R::LessEqual
                    },
                    word.operand_view(),
                    i64::from(i32::MAX),
                )]
            }),
            (false, Test::Half { above }) => Some(if wide {
                let operand = match operand.cast() {
                    Some((Encoding::UInt64FromInt64, _, _, inner)) => inner,
                    _ => operand,
                };
                vec![sign_condition(Ty::Int64, operand, above)]
            } else {
                let word = sign_cast(Ty::UInt32, Ty::Int32, operand);
                vec![sign_condition(Ty::Int32, word.operand_view(), above)]
            }),
            _ => None,
        }
    }
}

impl ConditionTerm {
    /// Root-only probes used when admitting signedness comparisons.
    pub(crate) fn names_sign_cast32(&self) -> bool {
        let Some(view) = comparison(self) else {
            return false;
        };
        matches!(view.format, Ty::Int32 | Ty::UInt32)
            && view.operands.iter().any(|operand| matches!(operand.operand_view().cast(),
                Some((Encoding::Generic, source, destination, _)) if crate::kernel::is_sign_cast32(source, destination)))
    }

    pub(crate) fn names_narrow_signedness_cast(&self) -> bool {
        let Some(view) = comparison(self) else {
            return false;
        };
        if view.format != Ty::Int32 && view.format.format().bits() >= 32 {
            return false;
        }
        let sign_cast = |term: View<'_>| {
            matches!(term.cast(),
            Some((Encoding::Generic, source, destination, _))
                if source.format().bits() == destination.format().bits()
                    && source.format().bits() < 32
                    && source.format().is_signed() != destination.format().is_signed())
        };
        view.operands.iter().any(|side| {
            let side = side.operand_view();
            sign_cast(side) || matches!(side.cast(), Some((Encoding::Generic, _, Ty::Int32, value)) if sign_cast(value))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelTermImport, MachineBinaryOp as Op, Variable};

    fn variable(n: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(n))
    }
    fn sum(format: Ty) -> MachineTerm {
        MachineTerm::Binary {
            format,
            op: Op::Add,
            left: Box::new(variable(189201)),
            right: Box::new(variable(189202)),
        }
    }
    fn shape(condition: ConditionTerm) -> (Ty, Relation, [MachineTerm; 2]) {
        let view = comparison(&condition).unwrap();
        (
            view.format,
            view.relation,
            view.operands.each_ref().map(|operand| {
                operand
                    .operand_view()
                    .retain(view.format)
                    .value()
                    .clone()
                    .constant_in32(view.format)
            }),
        )
    }
    fn shared_equivalents(
        context: &PureFactContext,
        native: &ConditionTerm,
    ) -> Option<Vec<ConditionTerm>> {
        let ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } = native
        else {
            panic!("comparison")
        };
        let expected = context
            .sign_bit_equivalents(native)
            .map(|conditions| conditions.into_iter().map(shape).collect::<Vec<_>>());
        let roots = [left, right].map(|term| {
            KernelTermImport::default()
                .machine_arithmetic(*format, term)
                .unwrap()
        });
        let shared =
            condition_for_operand_views(*format, *relation, roots.each_ref().map(View::Shared));
        assert_eq!(shared.names_sign_cast32(), native.names_sign_cast32());
        assert_eq!(
            shared.names_narrow_signedness_cast(),
            native.names_narrow_signedness_cast()
        );
        let exports = KernelTermExport::machine_export_count();
        let actual = context.sign_bit_equivalents(&shared);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            actual
                .clone()
                .map(|conditions| conditions.into_iter().map(shape).collect::<Vec<_>>()),
            expected,
            "{native:?}"
        );
        actual
    }

    #[test]
    fn shared_sign_bit_readings_keep_width_directions_and_written_casts() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        for format in [Ty::Int32, Ty::UInt32, Ty::Int64, Ty::UInt64] {
            let mut operands = vec![sum(format)];
            if format.format().bits() == 32 {
                let other = if format == Ty::Int32 {
                    Ty::UInt32
                } else {
                    Ty::Int32
                };
                operands.push(MachineTerm::sign_cast32(other, format, sum(other)));
                operands.push(MachineTerm::sign_cast32(
                    other,
                    format,
                    MachineTerm::sign_cast32(format, other, sum(format)),
                ));
            } else if format == Ty::UInt64 {
                operands.push(MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt64FromInt64,
                    Box::new(sum(Ty::Int64)),
                ));
            }
            let (relations, threshold) = if format.format().is_signed() {
                ([R::LessThan, R::GreaterEqual], 0)
            } else {
                (
                    [R::GreaterThan, R::LessEqual],
                    signed_maximum(format.format().bits()),
                )
            };
            for operand in operands {
                for relation in relations {
                    let native = bound(format, relation, View::Legacy(&operand), threshold);
                    let result = shared_equivalents(&context, &native).unwrap();
                    assert_eq!(result.len(), if format == Ty::Int64 { 2 } else { 1 });
                    let ConditionTerm::Compare { left, right, .. } = native else {
                        unreachable!()
                    };
                    let mirrored = match relation {
                        R::LessThan => R::GreaterThan,
                        R::LessEqual => R::GreaterEqual,
                        R::GreaterThan => R::LessThan,
                        R::GreaterEqual => R::LessEqual,
                        _ => unreachable!(),
                    };
                    shared_equivalents(
                        &context,
                        &ConditionTerm::machine_compare(format, mirrored, *right, *left),
                    )
                    .unwrap();
                }
            }
        }
    }

    #[test]
    fn fresh_shared_sign_bit_decisions_do_not_export_arithmetic() {
        use crate::kernel::{KernelTerm, KernelType};
        let _session = crate::kernel::VerificationSession::enter();
        let variable =
            KernelTerm::variable(KernelType::Program(Ty::UInt32.c_type()), Variable(189211));
        let prefix =
            KernelTerm::machine_binary_shared(Ty::UInt32, Op::Add, [variable.clone(), variable]);
        let mask = KernelTermImport::default()
            .machine_arithmetic(Ty::UInt32, &MachineTerm::uint32_constant(255))
            .unwrap();
        let masked = KernelTerm::machine_binary_shared(Ty::UInt32, Op::BitwiseAnd, [prefix, mask]);
        let cast =
            KernelTerm::machine_cast_shared(Encoding::Generic, Ty::UInt32, Ty::Int32, masked);
        let zero = MachineTerm::constant(0);
        let context = PureFactContext::new();
        for (relation, expected) in [(R::LessThan, false), (R::GreaterEqual, true)] {
            let query = condition_for_operand_views(
                Ty::Int32,
                relation,
                [View::Shared(&cast), View::Legacy(&zero)],
            );
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(context.decide_by_sign_bit(&query), Some(expected));
            assert_eq!(context.decide(&query), Some(expected));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
        let unsupported = bound(Ty::Int32, R::LessEqual, View::Shared(&cast), 42);
        let exports = KernelTermExport::machine_export_count();
        assert!(context.sign_bit_equivalents(&unsupported).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_signed_narrow_half_range_requires_both_carrier_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        for (source, destination, maximum) in [
            (Ty::Int8, Ty::UInt8, 127i32),
            (Ty::Int16, Ty::UInt16, 32767i32),
        ] {
            let operand = sum(Ty::Int32);
            let cast = MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: source,
                to: destination,
                value: Box::new(operand.clone()),
            };
            let query =
                ConditionTerm::signed_greater_than(cast, MachineTerm::constant(maximum as u32));
            let lower = ConditionTerm::signed_less_equal(
                MachineTerm::constant((-maximum - 1) as u32),
                operand.clone(),
            );
            let upper =
                ConditionTerm::signed_less_equal(operand, MachineTerm::constant(maximum as u32));
            for (has_lower, has_upper) in
                [(false, false), (true, false), (false, true), (true, true)]
            {
                let mut context = PureFactContext::new();
                if has_lower {
                    context = context.assume_condition(lower.clone(), true);
                }
                if has_upper {
                    context = context.assume_condition(upper.clone(), true);
                }
                assert_eq!(
                    shared_equivalents(&context, &query).is_some(),
                    has_lower && has_upper
                );
            }
        }
    }

    #[test]
    fn shared_narrow_sign_bit_readings_require_carrier_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        for (source, destination, max) in
            [(Ty::UInt8, Ty::Int8, 255), (Ty::UInt16, Ty::Int16, 65535)]
        {
            let operand = sum(Ty::Int32);
            let converted = MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: source,
                to: destination,
                value: Box::new(operand.clone()),
            };
            let query = ConditionTerm::signed_less_than(converted, MachineTerm::constant(0));
            assert!(shared_equivalents(&PureFactContext::new(), &query).is_none());
            let source = Proposition::ConditionIs(
                ConditionTerm::unsigned_less_equal(operand, MachineTerm::constant(max)),
                true,
            );
            let facts = PureFactContext::new().assume_proposition(source.clone());
            assert!(shared_equivalents(&facts, &query).is_some());
            // Use an independently weaker context for the missing-bound control.
            let weak = PureFactContext::new().assume_condition(
                ConditionTerm::unsigned_less_equal(sum(Ty::Int32), MachineTerm::constant(max + 1)),
                true,
            );
            assert!(shared_equivalents(&weak, &query).is_none());
        }
    }
}

#[cfg(test)]
#[path = "../../../scaling_tests/kernel/assumptions/condition_reasoning/sign_bit/tests.rs"]
mod scaling_tests;
