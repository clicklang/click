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
//! At 32 and 64 bits a conversion reuses the word (a 64-bit unsigned
//! reading of a signed value wraps it in `UInt64FromInt64`), so the rule is
//! the identity of one word's two readings and holds for every word. At 8
//! and 16 bits the conversion is a `MachineIntegerCast` of a canonical
//! carrier, read in an `int32` comparison; the rule holds when the operand
//! lies in its own format's range, which the context must decide.
//!
//! [`PureFactContext::decide_by_sign_bit`] answers one such comparison by
//! deciding its equivalent, and a lookup of a known condition also looks up
//! its equivalent: one rewrite of the root and one decision or lookup, with
//! no visit of any other fact. An 8- or 16-bit sign test names a cast no
//! plain comparison of its operand does, so assuming one also files its
//! operand's half-range test. The equivalent of the equivalent is the
//! original comparison, so the rule is not applied again inside it.

use super::*;
use crate::kernel::CompareRelation as R;
use crate::kernel::MachineIntegerType as Ty;

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

/// `term` as the constant it is at an `int32` or a 64-bit comparison.
fn constant(term: &Bitvector32Term) -> Option<i64> {
    match term {
        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => {
            Some(i64::from(*value))
        }
        Bitvector32Term::Int64Constant(value) => Some(*value),
        Bitvector32Term::UInt64Constant(value) => i64::try_from(*value).ok(),
        _ => None,
    }
}

/// The comparison with its constant on the right: `0 > w` is `w < 0`.
fn constant_on_the_right(
    relation: R,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(R, Bitvector32Term, i64)> {
    if let Some(value) = constant(right) {
        return Some((relation, left.clone(), value));
    }
    let value = constant(left)?;
    let mirrored = match relation {
        R::LessThan => R::GreaterThan,
        R::LessEqual => R::GreaterEqual,
        R::GreaterThan => R::LessThan,
        R::GreaterEqual => R::LessEqual,
        R::Equal => return None,
    };
    Some((mirrored, right.clone(), value))
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
        let ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } = condition
        else {
            return None;
        };
        let (relation, operand, value) = constant_on_the_right(*relation, left, right)?;
        let format = *format;
        let in_range = |term: &Bitvector32Term, lower: i64, upper: i64| {
            self.decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(lower as u32),
                term.clone(),
            )) == Some(true)
                && self.decide(&ConditionTerm::signed_less_equal(
                    term.clone(),
                    Bitvector32Term::Constant(upper as u32),
                )) == Some(true)
        };
        let constant = |value: i64| Bitvector32Term::Constant(value as u32);
        // An 8- or 16-bit conversion between the two signednesses of one
        // width, read in an `int32` comparison.
        if format == Ty::Int32
            && let Bitvector32Term::MachineIntegerCast {
                value: inner,
                source,
                destination,
            } = &operand
            && source.format().bits() == destination.format().bits()
            && source.format().bits() < 32
            && source.format().is_signed() != destination.format().is_signed()
        {
            let maximum = signed_maximum(source.format().bits());
            let inner = inner.as_ref().clone();
            return Some(match test(relation, value, maximum)? {
                // `(intN)u`'s sign is `u`'s half-range test.
                Test::Sign { negative } if destination.format().is_signed() => {
                    // An unsigned word at most `2^N - 1` is in `[0, 2^N - 1]`.
                    let unsigned_bound = self.decide(&ConditionTerm::unsigned_less_equal(
                        inner.clone(),
                        constant(2 * maximum + 1),
                    )) == Some(true);
                    if !unsigned_bound && !in_range(&inner, 0, 2 * maximum + 1) {
                        return None;
                    }
                    vec![if negative {
                        ConditionTerm::signed_greater_than(inner, constant(maximum))
                    } else {
                        ConditionTerm::signed_less_equal(inner, constant(maximum))
                    }]
                }
                // `(uintN)x`'s half-range test is `x`'s sign.
                Test::Half { above } if !destination.format().is_signed() => {
                    if !in_range(&inner, -maximum - 1, maximum) {
                        return None;
                    }
                    vec![if above {
                        ConditionTerm::signed_less_than(inner, constant(0))
                    } else {
                        ConditionTerm::signed_less_equal(constant(0), inner)
                    }]
                }
                _ => return None,
            });
        }
        // A 32- or 64-bit word read at both signednesses.
        let wide = match format {
            Ty::Int32 | Ty::UInt32 => false,
            Ty::Int64 | Ty::UInt64 => true,
            _ => return None,
        };
        let bits = format.format().bits();
        match (
            format.format().is_signed(),
            test(relation, value, signed_maximum(bits))?,
        ) {
            (true, Test::Sign { negative }) => Some(if wide {
                let maximum = Bitvector32Term::UInt64Constant(i64::MAX as u64);
                let unsigned = |word: Bitvector32Term| {
                    if negative {
                        ConditionTerm::uint64_greater_than(word, maximum.clone())
                    } else {
                        ConditionTerm::uint64_less_equal(word, maximum.clone())
                    }
                };
                vec![
                    unsigned(operand.clone()),
                    unsigned(Bitvector32Term::UInt64FromInt64(Box::new(operand))),
                ]
            } else {
                let maximum = constant(i64::from(i32::MAX));
                vec![if negative {
                    ConditionTerm::unsigned_greater_than(operand, maximum)
                } else {
                    ConditionTerm::unsigned_less_equal(operand, maximum)
                }]
            }),
            (false, Test::Half { above }) => Some(if wide {
                let operand = match operand {
                    Bitvector32Term::UInt64FromInt64(inner) => *inner,
                    operand => operand,
                };
                let zero = Bitvector32Term::Int64Constant(0);
                vec![if above {
                    ConditionTerm::int64_signed_less_than(operand, zero)
                } else {
                    ConditionTerm::int64_signed_less_equal(zero, operand)
                }]
            } else {
                vec![if above {
                    ConditionTerm::signed_less_than(operand, constant(0))
                } else {
                    ConditionTerm::signed_less_equal(constant(0), operand)
                }]
            }),
            _ => None,
        }
    }
}

impl ConditionTerm {
    /// Whether this is an `int32` comparison of an 8- or 16-bit conversion
    /// between the two signednesses of one width. One match on the root.
    pub(crate) fn names_narrow_signedness_cast(&self) -> bool {
        let ConditionTerm::Compare {
            format: Ty::Int32,
            left,
            right,
            ..
        } = self
        else {
            return false;
        };
        [left, right].into_iter().any(|side| {
            matches!(
                side.as_ref(),
                Bitvector32Term::MachineIntegerCast { source, destination, .. }
                    if source.format().bits() == destination.format().bits()
                        && source.format().bits() < 32
                        && source.format().is_signed() != destination.format().is_signed()
            )
        })
    }
}
