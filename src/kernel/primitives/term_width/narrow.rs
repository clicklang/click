//! The canonical carrier of a narrow value.
//!
//! An 8- or 16-bit machine value (and C `_Bool`) rides in a 32-bit word,
//! and that word is the canonical element of its format: the sign extension
//! of a signed value, the zero extension of an unsigned one. This module
//! says, from a word's construction alone, whether it is such a carrier.

use super::*;

/// Why a word at a narrow format is not, by its construction, the canonical
/// carrier of a value of that format.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NarrowCarrierViolation {
    pub(crate) format: MachineIntegerType,
    /// The node that is not canonical, e.g. `Add`.
    pub(crate) shape: &'static str,
}

impl std::fmt::Display for NarrowCarrierViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "a {:?} value's word ({}) is not a canonical carrier of its format",
            self.format, self.shape
        )
    }
}

fn is_narrow(ty: MachineIntegerType) -> bool {
    ty.format().bits() < 32
}

/// The narrow format a load of `kind` reads.
fn narrow_load_format(kind: LoadKind) -> Option<MachineIntegerType> {
    match kind {
        LoadKind::Int8 => Some(MachineIntegerType::Int8),
        LoadKind::UInt8 => Some(MachineIntegerType::UInt8),
        LoadKind::Int16 => Some(MachineIntegerType::Int16),
        LoadKind::UInt16 => Some(MachineIntegerType::UInt16),
        _ => None,
    }
}

/// A word that is canonical for `inner` is canonical for every format of at
/// most 32 bits that contains `inner`: extension composes.
fn contains(ty: MachineIntegerType, inner: MachineIntegerType) -> bool {
    ty.format().bits() <= 32 && ty.format().contains(inner.format())
}

/// The shape name of a word, for a violation's report.
fn shape(word: &Bitvector32Term) -> &'static str {
    use Bitvector32Term as T;
    match word {
        T::Constant(_) => "an out-of-range constant",
        T::Variable(_) => "Variable",
        T::MemoryLoad(..) => "a load of another kind",
        T::MachineIntegerCast { .. } => "a cast to another format",
        T::IntegerToMachine { .. } => "an Integer conversion to another format",
        T::If { .. } => "If",
        T::Add(..) => "Add",
        T::Subtract(..) => "Subtract",
        T::Multiply(..) => "Multiply",
        T::Divide(..) | T::UnsignedDivide(..) => "Divide",
        T::Remainder(..) | T::UnsignedRemainder(..) => "Remainder",
        T::ShiftLeft(..) => "ShiftLeft",
        T::ArithmeticShiftRight(..) | T::LogicalShiftRight(..) => "ShiftRight",
        T::BitwiseAnd(..) => "BitwiseAnd",
        T::BitwiseOr(..) => "BitwiseOr",
        T::BitwiseXor(..) => "BitwiseXor",
        T::BitwiseNot(..) => "BitwiseNot",
        T::UInt32From64(..) => "UInt32From64",
        T::PureFunctionApplication { .. } => "PureFunctionApplication",
        T::ClickFunctionApplication { .. } => "ClickFunctionApplication",
        T::AlgebraicMatch { .. } => "AlgebraicMatch",
        T::RangeFold { .. } => "RangeFold",
        _ => "a word of another width",
    }
}

/// Whether `word`, read at the narrow format `ty`, is by construction the
/// canonical carrier of a `ty` value. `Err` names the first node that is not.
///
/// A variable that is not a registered load is accepted as a binder of the
/// format, whose introduction states its range. This is the debug check of
/// the producers' invariant; the kernel's own rules use
/// [`narrow_word_is_syntactic_carrier`], which trusts no binder.
pub(crate) fn narrow_carrier_violation(
    ty: MachineIntegerType,
    word: &Bitvector32Term,
) -> Result<(), NarrowCarrierViolation> {
    carrier_violation(ty, word, true)
}

/// Whether `word`, read at the narrow format `ty`, is the canonical carrier
/// of a `ty` value by its construction alone: as
/// [`narrow_carrier_violation`], except that an unregistered variable,
/// anywhere in the word, is not one. A kernel rule that relies on a
/// binder's range must find that range among its premises.
pub(crate) fn narrow_word_is_syntactic_carrier(
    ty: MachineIntegerType,
    word: &Bitvector32Term,
) -> bool {
    carrier_violation(ty, word, false).is_ok()
}

fn carrier_violation(
    ty: MachineIntegerType,
    word: &Bitvector32Term,
    binders: bool,
) -> Result<(), NarrowCarrierViolation> {
    use Bitvector32Term as T;
    let narrow_carrier_violation = |ty, word| carrier_violation(ty, word, binders);
    let violation = |word: &Bitvector32Term| {
        Err(NarrowCarrierViolation {
            format: ty,
            shape: shape(word),
        })
    };
    if !is_narrow(ty) {
        return Ok(());
    }
    match word {
        T::Constant(_) => match ty.constant_from_term(word) {
            Some(_) => Ok(()),
            None => violation(word),
        },
        T::MemoryLoad(_, _, kind) => match narrow_load_format(*kind) {
            Some(loaded) if contains(ty, loaded) => Ok(()),
            _ => violation(word),
        },
        T::Variable(variable) => match crate::kernel::registered_load_kind_for_variable(variable) {
            Some(kind) => match narrow_load_format(kind) {
                Some(loaded) if contains(ty, loaded) => Ok(()),
                _ => violation(word),
            },
            // Any other variable at a narrow format is a binder of that
            // format: a parameter, a theorem or quantifier binder, or a
            // fresh value a loop or call produced. Its introduction states
            // its range (`c_narrow_integer_range_facts`), which makes it the
            // canonical carrier on every path that names it.
            None if binders => Ok(()),
            None => violation(word),
        },
        T::MachineIntegerCast { destination, .. } if contains(ty, *destination) => Ok(()),
        T::IntegerToMachine { destination, .. } if contains(ty, *destination) => Ok(()),
        // Rule C1c: a `Bool`'s cast is the word 1 or 0, canonical at every
        // format.
        T::BoolCast { .. } => Ok(()),
        T::If {
            then_term,
            else_term,
            ..
        } => {
            narrow_carrier_violation(ty, then_term)?;
            narrow_carrier_violation(ty, else_term)
        }
        // Zero extension survives a mask by anything; sign extension
        // survives the bitwise operations of two sign-extended words.
        T::BitwiseAnd(left, right) if !ty.format().is_signed() => {
            narrow_carrier_violation(ty, left).or_else(|_| narrow_carrier_violation(ty, right))
        }
        T::BitwiseAnd(left, right) | T::BitwiseOr(left, right) | T::BitwiseXor(left, right) => {
            narrow_carrier_violation(ty, left)?;
            narrow_carrier_violation(ty, right)
        }
        T::BitwiseNot(value) if ty.format().is_signed() => narrow_carrier_violation(ty, value),
        // A modular conversion into a signed narrow format spells the sign
        // extension of the low bits: `((w & mask) ^ sign) - sign`.
        T::Subtract(left, sign)
            if ty.format().is_signed()
                && **sign == T::Constant(1 << (ty.format().bits() - 1))
                && let T::BitwiseXor(a, b) = left.as_ref()
                && let Some(masked) = (a == sign).then_some(b).or((b == sign).then_some(a))
                && let T::BitwiseAnd(a, b) = masked.as_ref()
                && [a, b]
                    .iter()
                    .any(|side| ***side == T::Constant((1 << ty.format().bits()) - 1)) =>
        {
            Ok(())
        }
        _ => violation(word),
    }
}

/// The narrow format of a value's tag, `_Bool` read as its `uint8` carrier.
fn value_narrow_format(value: &CValue) -> Option<(MachineIntegerType, &Bitvector32Term)> {
    Some(match value {
        CValue::Bool(term) | CValue::UInt8(term) => (MachineIntegerType::UInt8, term),
        CValue::Int8(term) => (MachineIntegerType::Int8, term),
        CValue::Int16(term) => (MachineIntegerType::Int16, term),
        CValue::UInt16(term) => (MachineIntegerType::UInt16, term),
        _ => return None,
    })
}

/// The first narrow position of `value`, or of a term inside it, whose word
/// is not a canonical carrier.
pub(crate) fn value_narrow_violation(value: &CValue) -> Option<NarrowCarrierViolation> {
    if let Some((ty, term)) = value_narrow_format(value)
        && let Err(violation) = narrow_carrier_violation(ty, term)
    {
        return Some(violation);
    }
    let term = crate::kernel::spec::c_value_bitvector_term(value.numeric_value())?;
    NarrowWalk::default().term(&term)
}

/// The first narrow position inside `condition` -- an observation of a
/// narrow format, or a conversion from one -- whose word is not a canonical
/// carrier.
pub(crate) fn condition_narrow_violation(
    condition: &ConditionTerm,
) -> Option<NarrowCarrierViolation> {
    NarrowWalk::default().condition(condition)
}

/// One walk over a condition or term. Integer nodes are shared, so each is
/// visited once.
#[derive(Default)]
struct NarrowWalk {
    seen: std::collections::HashSet<u64>,
}

impl NarrowWalk {
    fn condition(&mut self, condition: &ConditionTerm) -> Option<NarrowCarrierViolation> {
        match condition {
            crate::kernel::binary_bitvector_condition!(left, right) => {
                self.term(left).or_else(|| self.term(right))
            }
            crate::kernel::integer_comparison_condition!(left, right) => {
                self.integer(left).or_else(|| self.integer(right))
            }
            _ => None,
        }
    }

    fn term(&mut self, term: &Bitvector32Term) -> Option<NarrowCarrierViolation> {
        use Bitvector32Term as T;
        match term {
            T::MachineIntegerCast { value, source, .. } => narrow_carrier_violation(*source, value)
                .err()
                .or_else(|| self.term(value)),
            T::If {
                condition,
                then_term,
                else_term,
            } => self
                .condition(condition)
                .or_else(|| self.term(then_term))
                .or_else(|| self.term(else_term)),
            T::IntegerToMachine { value, .. } => self.integer(value),
            T::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => [start, end, initial, body]
                .into_iter()
                .find_map(|term| self.term(term)),
            T::PureFunctionApplication { arguments, .. } => {
                arguments.iter().find_map(|term| self.term(term))
            }
            term => {
                if let Some((_, left, right)) = term.as_binary() {
                    self.term(left).or_else(|| self.term(right))
                } else if let Some((_, value)) = term.as_unary() {
                    self.term(value)
                } else {
                    None
                }
            }
        }
    }

    fn integer(&mut self, term: &SharedIntegerTerm) -> Option<NarrowCarrierViolation> {
        if !self.seen.insert(term.id()) {
            return None;
        }
        match term.as_ref() {
            IntegerTerm::Machine(machine) => {
                narrow_carrier_violation(machine.ty(), machine.value())
                    .err()
                    .or_else(|| self.term(machine.value()))
            }
            IntegerTerm::Negate(value) => self.integer(value),
            crate::kernel::binary_integer_term!(left, right) => {
                self.integer(left).or_else(|| self.integer(right))
            }
            IntegerTerm::RangeFold { initial, body, .. } => {
                self.integer(initial).or_else(|| self.integer(body))
            }
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => self
                .condition(condition)
                .or_else(|| self.integer(then_term))
                .or_else(|| self.integer(else_term)),
            IntegerTerm::PureFunctionApplication(application) => application
                .arguments()
                .iter()
                .find_map(|argument| match argument {
                    PureFunctionArgument::Integer(value) => self.integer(value),
                    _ => None,
                }),
            IntegerTerm::Constant(_)
            | IntegerTerm::Variable(_)
            | IntegerTerm::AlgebraicMatch { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use MachineIntegerType as Ty;

    fn var(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(index))
    }

    #[test]
    fn canonical_carriers_are_accepted() {
        let word = var(171_001);
        let cast = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::Int8, word.clone());
        for (ty, carrier) in [
            (Ty::Int8, Bitvector32Term::Constant(-5i32 as u32)),
            (Ty::UInt8, Bitvector32Term::Constant(200)),
            (Ty::Int8, word.clone()),
            (Ty::Int8, cast.clone()),
            // A canonical `int8` word is canonical for `int16` too.
            (Ty::Int16, cast.clone()),
            (
                Ty::UInt8,
                Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(255)),
            ),
            (
                Ty::Int8,
                Bitvector32Term::subtract(
                    Bitvector32Term::bitwise_xor(
                        Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(255)),
                        Bitvector32Term::Constant(128),
                    ),
                    Bitvector32Term::Constant(128),
                ),
            ),
            (
                Ty::Int8,
                Bitvector32Term::if_then_else(
                    ConditionTerm::equal(word.clone(), Bitvector32Term::Constant(0)),
                    cast.clone(),
                    Bitvector32Term::Constant(1),
                ),
            ),
        ] {
            assert_eq!(
                narrow_carrier_violation(ty, &carrier),
                Ok(()),
                "{carrier:?}"
            );
        }
    }

    #[test]
    fn non_canonical_words_are_refused() {
        let word = var(171_002);
        let sum = Bitvector32Term::add(word.clone(), Bitvector32Term::Constant(1));
        let signed = Bitvector32Term::machine_integer_cast(Ty::Int32, Ty::Int8, word.clone());
        for (ty, carrier) in [
            (Ty::UInt8, sum.clone()),
            (Ty::Int8, Bitvector32Term::Constant(200)),
            // A signed byte's word is not an unsigned byte's.
            (Ty::UInt8, signed),
            (
                Ty::Int8,
                Bitvector32Term::bitwise_and(word.clone(), Bitvector32Term::Constant(255)),
            ),
        ] {
            assert!(
                narrow_carrier_violation(ty, &carrier).is_err(),
                "{ty:?} {carrier:?}"
            );
        }
        assert!(value_narrow_violation(&CValue::UInt8(sum.clone())).is_some());
        // A narrow observation inside a condition is checked too.
        let observed = IntegerTerm::from_machine(Ty::UInt8, sum).unwrap();
        let condition = ConditionTerm::integer_less_equal(observed, IntegerTerm::constant_i64(9));
        assert!(condition_narrow_violation(&condition).is_some());
        let canonical = IntegerTerm::from_machine(Ty::UInt8, word).unwrap();
        let condition = ConditionTerm::integer_less_equal(canonical, IntegerTerm::constant_i64(9));
        assert_eq!(condition_narrow_violation(&condition), None);
    }
}
