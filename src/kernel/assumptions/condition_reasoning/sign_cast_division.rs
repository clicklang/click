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
use crate::kernel::MachineIntegerType as Ty;

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
fn division_at(
    format: Ty,
    op: Op,
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (format, op) {
        (Ty::Int32, Op::Divide) => Bitvector32Term::divide(left, right),
        (Ty::Int32, _) => Bitvector32Term::remainder(left, right),
        (_, Op::Divide) => Bitvector32Term::unsigned_divide(left, right),
        (_, _) => Bitvector32Term::unsigned_remainder(left, right),
    }
}

impl ConditionTerm {
    /// Whether this is a 32-bit comparison with a side that is σ of a
    /// quotient or remainder, which rule C reads. One match on the root and
    /// each side.
    pub(crate) fn names_sign_cast_division(&self) -> bool {
        matches!(
            self,
            ConditionTerm::Compare {
                format: Ty::Int32 | Ty::UInt32,
                left,
                right,
                ..
            } if left.sign_cast_division_operands().is_some()
                || right.sign_cast_division_operands().is_some()
        )
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
        let ConditionTerm::Compare {
            format: format @ (Ty::Int32 | Ty::UInt32),
            relation,
            left,
            right,
        } = condition
        else {
            return None;
        };
        if left.sign_cast_division_operands().is_none()
            && right.sign_cast_division_operands().is_none()
        {
            return None;
        }
        let _deciding = Deciding::enter();
        let left_reading = self.sign_cast_division_reading(left);
        let right_reading = self.sign_cast_division_reading(right);
        if left_reading.is_none() && right_reading.is_none() {
            return None;
        }
        Some(ConditionTerm::machine_compare(
            *format,
            *relation,
            left_reading.unwrap_or_else(|| left.as_ref().clone()),
            right_reading.unwrap_or_else(|| right.as_ref().clone()),
        ))
    }

    /// σ of a quotient or remainder `term` read at the other signedness:
    /// the operator there over σ of its operands, when this context decides
    /// the dividend's `int32` reading nonnegative and the divisor's
    /// positive. `None` otherwise.
    fn sign_cast_division_reading(&self, term: &Bitvector32Term) -> Option<Bitvector32Term> {
        let (source, op, dividend, divisor) = term.sign_cast_division_operands()?;
        let destination = other(source);
        let cast = |value: &Bitvector32Term| {
            Bitvector32Term::sign_cast32(source, destination, value.clone())
        };
        let (cast_dividend, cast_divisor) = (cast(dividend), cast(divisor));
        // The operands' `int32` readings: the operands themselves at
        // `int32`, their σ at `uint32`.
        let (signed_dividend, signed_divisor) = if source == Ty::Int32 {
            (dividend.clone(), divisor.clone())
        } else {
            (cast_dividend.clone(), cast_divisor.clone())
        };
        let zero = || Bitvector32Term::Constant(0);
        if self.decide(&ConditionTerm::signed_less_equal(zero(), signed_dividend)) != Some(true)
            || self.decide(&ConditionTerm::signed_less_than(zero(), signed_divisor)) != Some(true)
        {
            return None;
        }
        Some(division_at(destination, op, cast_dividend, cast_divisor))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;

    fn var(id: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(id))
    }

    fn sigma(source: Ty, value: Bitvector32Term) -> Bitvector32Term {
        Bitvector32Term::sign_cast32(source, other(source), value)
    }

    fn signed_nonnegative(value: Bitvector32Term) -> ConditionTerm {
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value)
    }

    fn signed_positive(value: Bitvector32Term) -> ConditionTerm {
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value)
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
                Bitvector32Term::UInt32Constant(0)
            )),
            Some(false)
        );
        assert_eq!(
            context.decide(&ConditionTerm::unsigned_less_equal(
                d,
                Bitvector32Term::UInt32Constant(i32::MAX as u32)
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
                Bitvector32Term::unsigned_divide(n.clone(), d.clone()),
            ),
            Bitvector32Term::divide(sigma(Ty::UInt32, n), sigma(Ty::UInt32, d)),
        );
        assert_eq!(context.decide_by_sign_cast_division(&equality), None);
    }
}
