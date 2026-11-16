//! Signed-machine affine and interval computations for arithmetic planning.
//! Internal plans expand into ordinary bounds and observation identities.
use super::super::{BitvectorBinaryOp, ConditionTerm, MachineTerm, Proposition, Variable};
use crate::kernel::CompareRelation;
use crate::kernel::MachineBinaryOp;
use crate::kernel::MachineIntegerType;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{bits32_constant, constant_u32, constant_u64, uint64_constant};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

mod atom_keys;
mod shared_operands;
pub(crate) use shared_operands::clear_shared_operand_keys;

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;

/// Carriers are explicit even though this first checker accepts only signed
/// int32.  Keeping the carrier on every result prevents a future widening or
/// signedness extension from silently changing an existing certificate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(
    dead_code,
    reason = "planned carriers are part of the typed boundary before their checkers exist"
)]
pub(crate) enum SignedArithmeticCarrier {
    SignedInt32,
    SignedInt64,
    UnsignedInt32,
    UnsignedInt64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SignedArithmeticRelation {
    LessEqual,
    Equal,
    Disequal,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum SignedArithmeticAtomToken {
    Constant(u32),
    Read(crate::kernel::KernelTerm),
    Variable(Variable),
    // An opaque signed observation of the low word; it carries no fact
    // about the original 64-bit value. Keep its identity distinct.
    Narrow64Variable(Variable),
    Narrow64Expression,
    NativeConstant(u64),
    NativeBinary(BitvectorBinaryOp),
    PureFunction {
        name: String,
        arity: usize,
    },
    Binary(BitvectorBinaryOp),
    UnaryNot,
    /// A C integer conversion of the following operand, as an opaque
    /// observation; `IntervalNarrowedCast` alone relates it to the operand.
    Cast {
        source: crate::kernel::MachineIntegerType,
        destination: crate::kernel::MachineIntegerType,
    },
}

/// Structural identity for the supported signed-machine term fragment.
/// The common term interner retains arithmetic sharing; claim maps compare
/// handles rather than repeatedly hashing expanded token sequences.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct SignedArithmeticAtom {
    key: crate::kernel::KernelTerm,
    opaque_root: bool,
    opaque_parts: bool,
    small_word_literal: bool,
}

impl Ord for SignedArithmeticAtom {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            self.key.id(),
            self.opaque_root,
            self.opaque_parts,
            self.small_word_literal,
        )
            .cmp(&(
                other.key.id(),
                other.opaque_root,
                other.opaque_parts,
                other.small_word_literal,
            ))
    }
}
impl PartialOrd for SignedArithmeticAtom {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl SignedArithmeticAtom {
    pub(crate) fn from_term(term: &MachineTerm) -> Option<Self> {
        signed_arithmetic_atom_key(term)
    }

    #[cfg(test)]
    pub(crate) fn from_operand(value: crate::kernel::MachineOperandView<'_>) -> Option<Self> {
        match value {
            crate::kernel::MachineOperandView::Legacy(value) => Self::from_term(value),
            crate::kernel::MachineOperandView::Shared(value) => atom_keys::from_shared(value),
        }
    }

    pub(crate) fn from_canonical_operand(
        value: crate::kernel::MachineOperandView<'_>,
    ) -> Option<Self> {
        match value {
            crate::kernel::MachineOperandView::Legacy(value) => {
                Self::from_term(&canonical_term_budgeted(value)?)
            }
            crate::kernel::MachineOperandView::Shared(value) => {
                atom_keys::from_observation(value, MachineIntegerType::Int32)
            }
        }
    }

    pub(crate) fn work(&self) -> usize {
        // Construction pays for the selected syntax. A retained map key has
        // constant-size hashing, ordering and equality.
        1
    }

    pub(crate) fn as_variable(&self) -> Option<Variable> {
        match self.key.node() {
            crate::kernel::KernelTermNode::Variable(variable) => Some(*variable),
            _ => None,
        }
    }

    #[cfg(test)]
    fn is_opaque_root(&self) -> bool {
        self.opaque_root
    }
}

fn signed_arithmetic_atom_key(root: &MachineTerm) -> Option<SignedArithmeticAtom> {
    let mut tokens = Vec::new();
    let mut pending = vec![root];
    macro_rules! push_token {
        ($token:expr) => {{
            let growth = if tokens.len() == tokens.capacity() {
                tokens.capacity().max(1)
            } else {
                1
            };
            if crate::instrumentation::deadline_exceeded_with_work(growth) {
                return None;
            }
            tokens.push($token);
        }};
    }
    while let Some(term) = pending.pop() {
        let units = match term {
            bits32_constant!(value) => {
                (u32::BITS - constant_u32(*value).leading_zeros()) as usize + 2
            }
            MachineTerm::Variable(_) => 2,
            MachineTerm::PureFunctionApplication { name, arguments } => {
                name.len().saturating_add(arguments.len()).saturating_add(3)
            }
            unary_term!(Int32, BitwiseNot, _) => 2,
            term if signed_binary(term).is_some() => 3,
            _ => 1,
        };
        if crate::instrumentation::deadline_exceeded_with_work(units) {
            return None;
        }
        match term {
            bits32_constant!(value) => {
                push_token!(SignedArithmeticAtomToken::Constant(constant_u32(*value)));
            }
            MachineTerm::Variable(variable) => {
                push_token!(SignedArithmeticAtomToken::Variable(*variable));
            }
            MachineTerm::MemoryLoad(..) => {
                let read = crate::kernel::KernelTermImport::default()
                    .machine_arithmetic(MachineIntegerType::Int32, term)?;
                push_token!(SignedArithmeticAtomToken::Read(read));
            }
            cast_term!(UInt32From64, value) => {
                if let MachineTerm::Variable(variable) = value.as_ref() {
                    push_token!(SignedArithmeticAtomToken::Narrow64Variable(*variable));
                    continue;
                }
                // The full native expression is an opaque signed low-word
                // observation. Encode its identity iteratively, without
                // assuming that its arithmetic does not wrap or deriving any
                // bound on its signed result.
                push_token!(SignedArithmeticAtomToken::Narrow64Expression);
                let mut native_pending = vec![value.as_ref()];
                while let Some(native) = native_pending.pop() {
                    if crate::instrumentation::deadline_exceeded_with_work(1) {
                        return None;
                    }
                    let (operator, left, right) = match native {
                        MachineTerm::Variable(variable) => {
                            push_token!(SignedArithmeticAtomToken::Variable(*variable));
                            continue;
                        }
                        MachineTerm::MemoryLoad(..) => {
                            let read = crate::kernel::KernelTermImport::default()
                                .machine_arithmetic(MachineIntegerType::Int32, native)?;
                            push_token!(SignedArithmeticAtomToken::Read(read));
                            continue;
                        }
                        uint64_constant!(value) => {
                            push_token!(SignedArithmeticAtomToken::NativeConstant(constant_u64(
                                *value
                            )));
                            continue;
                        }
                        native => match native.as_binary() {
                            Some(
                                binary @ (
                                    BitvectorBinaryOp::Machine(
                                        MachineIntegerType::UInt64,
                                        MachineBinaryOp::Add
                                        | MachineBinaryOp::Subtract
                                        | MachineBinaryOp::Multiply
                                        | MachineBinaryOp::Divide
                                        | MachineBinaryOp::Remainder,
                                    ),
                                    _,
                                    _,
                                ),
                            ) => binary,
                            _ => return None,
                        },
                    };
                    push_token!(SignedArithmeticAtomToken::NativeBinary(operator));
                    native_pending.push(right);
                    native_pending.push(left);
                }
            }
            MachineTerm::PureFunctionApplication { name, arguments } => {
                push_token!(SignedArithmeticAtomToken::PureFunction {
                    name: name.clone(),
                    arity: arguments.len(),
                });
                pending.extend(arguments.iter().rev());
            }
            unary_term!(Int32, BitwiseNot, operand) => {
                push_token!(SignedArithmeticAtomToken::UnaryNot);
                pending.push(operand);
            }
            term if let Some((value, source, destination)) = widened_narrowed_cast(term) => {
                push_token!(SignedArithmeticAtomToken::Cast {
                    source,
                    destination,
                });
                pending.push(value);
            }
            // The `int32` widening of an 8- or 16-bit value is that value: an
            // opaque observation of its operand, as a 32-bit variable is.
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination @ MachineIntegerType::Int32,
            } if source.format().bits() < 32 => {
                push_token!(SignedArithmeticAtomToken::Cast {
                    source: *source,
                    destination: *destination,
                });
                pending.push(value);
            }
            // σ, the 32-bit sign cast, is a node of its own: `u as int32` is
            // an opaque observation of its operand, as a variable is.
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                from: source,
                to: destination,
            } if crate::kernel::is_sign_cast32(*source, *destination) => {
                push_token!(SignedArithmeticAtomToken::Cast {
                    source: *source,
                    destination: *destination,
                });
                pending.push(value);
            }
            term => {
                let (operator, left, right) = signed_binary(term)?;
                push_token!(SignedArithmeticAtomToken::Binary(operator));
                pending.push(right);
                pending.push(left);
            }
        }
    }
    atom_keys::from_tokens(tokens)
}

/// A 32-bit operation of the supported signed fragment: an `int32`
/// operator, or the logical right shift of a word. The unsigned division
/// and remainder read their operands unsigned, so they stay out, and so
/// does a `uint32` sign-free operator: the fragment reads its result as an
/// `int32` value, which a `uint32` one is only through σ (decision G7,
/// `design/machine-integers.md`; such a certificate is refused, and its
/// author writes the `int32` value).
fn signed_binary(term: &MachineTerm) -> Option<(BitvectorBinaryOp, &MachineTerm, &MachineTerm)> {
    term.as_binary().filter(|(operator, _, _)| {
        matches!(
            operator,
            BitvectorBinaryOp::Machine(crate::kernel::MachineIntegerType::Int32, _)
                | BitvectorBinaryOp::Machine(
                    crate::kernel::MachineIntegerType::UInt32,
                    crate::kernel::MachineBinaryOp::ShiftRight
                )
        )
    })
}

/// A normalized signed-machine affine proposition.
///
/// The invariant is `sum(terms * atoms) + constant relation 0`.  For example,
/// `x <= 5` is stored as `x - 5 <= 0`, while `x == 5` is stored as
/// `x - 5 == 0`; there is no separate RHS convention for equality.  Keeping
/// one zero-centered convention makes equality-to-order and interval
/// extraction local checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticClaim {
    pub(crate) carrier: SignedArithmeticCarrier,
    pub(crate) relation: SignedArithmeticRelation,
    pub(crate) terms: BTreeMap<SignedArithmeticAtom, BigInt>,
    pub(crate) constant: BigInt,
}

/// Claimed endpoints for an interval.  The expression identity is held in
/// the checker's linear term arena and operation nodes refer to child handles;
/// repeating a deep expression in every result would make a deep certificate
/// quadratic before checking began.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticInterval {
    pub(crate) carrier: SignedArithmeticCarrier,
    pub(crate) lower: i64,
    pub(crate) upper: i64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SignedArithmeticComparison {
    LessThan,
    LessEqual,
    Equal,
    Disequal,
    /// The `uint32` order of the two words, decided from their signed
    /// intervals once each has a known sign: a non-negative word reads the
    /// same unsigned, a negative one `2^32` more.
    UnsignedLessThan,
    UnsignedLessEqual,
}

/// The 32-bit reading of a conversion `IntervalNarrowedCast` may relate to
/// its operand: the `int32` widening `Cast(D -> Int32, Cast(S -> D, x))` of
/// a narrowing ([`narrowed_word_cast`]), with its operand `x`, `S` and `D`.
/// An 8- or 16-bit value is a value of its own width, so its 32-bit
/// observation is its widening, which every one- and two-byte value keeps.
/// One match on the root.
pub(crate) fn widened_narrowed_cast(
    term: &MachineTerm,
) -> Option<(
    &MachineTerm,
    crate::kernel::MachineIntegerType,
    crate::kernel::MachineIntegerType,
)> {
    let MachineTerm::Cast {
        spelling: MachineCastSpelling::Generic,
        value: narrowed,
        from: widened_from,
        to: crate::kernel::MachineIntegerType::Int32,
    } = term
    else {
        return None;
    };
    let MachineTerm::Cast {
        spelling: MachineCastSpelling::Generic,
        value,
        from: source,
        to: destination,
    } = narrowed.as_ref()
    else {
        return None;
    };
    (widened_from == destination && narrowed_word_cast(*source, *destination)).then_some((
        value,
        *source,
        *destination,
    ))
}

/// A conversion `IntervalNarrowedCast` may relate to its operand: from a
/// type carried exactly in a 32-bit word into a one- or two-byte type that
/// does not contain it.
pub(crate) fn narrowed_word_cast(
    source: crate::kernel::MachineIntegerType,
    destination: crate::kernel::MachineIntegerType,
) -> bool {
    source.format().bits() <= 32
        && crate::kernel::assumptions::narrowed_cast_identity(
            &MachineTerm::constant(0),
            source,
            destination,
        )
        .is_some()
}

/// One topologically ordered local derivation node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SignedArithmeticNode {
    Premise {
        index: usize,
        result: SignedArithmeticClaim,
    },
    Scale {
        source: usize,
        coefficient: BigInt,
        result: SignedArithmeticClaim,
    },
    Add {
        left: usize,
        right: usize,
        result: SignedArithmeticClaim,
    },
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: SignedArithmeticClaim,
    },
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: SignedArithmeticClaim,
    },
    /// Sharpen a non-strict bound with a disequality over the same affine
    /// form: `t <= 0` and `t != 0` give `t + 1 <= 0`, an integer fact.
    StrictFromDisequal {
        bound: usize,
        disequal: usize,
        result: SignedArithmeticClaim,
    },
    Trivial {
        result: SignedArithmeticClaim,
    },
    /// The int32 range of one opaque atom as an affine bound: `t <=
    /// INT32_MAX` or `INT32_MIN <= t`, true of every int32 value. It is the
    /// bound that lets a strict premise `x < y` bound `x` by
    /// `INT32_MAX - 1` when nothing else bounds `y`. Only an opaque root
    /// (a variable or pure-function application) qualifies, as for
    /// [`SignedArithmeticNode::IntervalAtom`].
    Int32Range {
        result: SignedArithmeticClaim,
    },
    /// Obtain an interval for an exact one-atom affine bound.
    IntervalFromAffine {
        source: usize,
        term: MachineTerm,
        lower: i64,
        upper: i64,
    },
    /// Import an exact affine bound whose atom is a compound machine term.
    /// This does not decompose or evaluate the operation: the source premise
    /// is the evidence for the already-evaluated term, and later nodes retain
    /// that exact term identity.
    IntervalFromAffineDirect {
        source: usize,
        term: MachineTerm,
        lower: i64,
        upper: i64,
    },
    IntervalIntersect {
        left: usize,
        right: usize,
        result: SignedArithmeticInterval,
    },
    /// An opaque atom has the complete signed-int32 interval.
    IntervalAtom {
        carrier: SignedArithmeticCarrier,
        term: MachineTerm,
        lower: i64,
        upper: i64,
    },
    DefinedPremise {
        index: usize,
        carrier: SignedArithmeticCarrier,
        term: MachineTerm,
    },
    IntervalAdd {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    /// Add two intervals whose endpoint sum is already within int32.  The
    /// child intervals therefore establish definedness without requiring a
    /// separate source-level overflow proposition.
    IntervalAddBounded {
        left: usize,
        right: usize,
        result: SignedArithmeticInterval,
    },
    IntervalSubtract {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalMultiply {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    /// Remainder after a bounded addition, using a checked interval for the
    /// original remainder. Both the original and resulting dividends are nonnegative.
    IntervalRemainderAdd {
        operand: usize,
        remainder: usize,
        addend: i32,
        divisor: i32,
        result: SignedArithmeticInterval,
    },
    IntervalRemainder {
        operand: usize,
        divisor: i32,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalShiftLeft {
        operand: usize,
        shift: i32,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalArithmeticShiftRight {
        operand: usize,
        shift: i32,
        result: SignedArithmeticInterval,
    },
    IntervalBitwiseAnd {
        operand: usize,
        mask: u32,
        // Bitwise-and is total for signed int32 values.  UB-sensitive work
        // needed to construct `operand` is checked by its child interval
        // nodes, so this node intentionally has no definedness reference.
        result: SignedArithmeticInterval,
    },
    /// A C conversion of a 32-bit-word operand into a one- or two-byte type
    /// whose operand interval lies inside the destination range: the
    /// conversion leaves the value unchanged (`narrowed_cast_identity`), so
    /// it has the operand's interval and, as affine evidence, the operand's
    /// affine form.
    IntervalNarrowedCast {
        operand: usize,
        source: crate::kernel::MachineIntegerType,
        destination: crate::kernel::MachineIntegerType,
        result: SignedArithmeticInterval,
    },
    IntervalCompare {
        left: usize,
        right: usize,
        comparison: SignedArithmeticComparison,
        result: Proposition,
    },
    /// Flatten a selected premise only with checked interval evidence for
    /// both expression roots. The source must be an ordinary premise node.
    AffinePremise {
        source: usize,
        left_evidence: usize,
        right_evidence: usize,
        result: SignedArithmeticClaim,
    },
    /// Re-express an interval-justified affine machine term as a checked
    /// proposition.  The source affine node supplies the algebraic fact;
    /// the interval node proves that every decomposed machine operation is
    /// defined (or has bounded endpoints).
    AffineConclusion {
        source: usize,
        evidence: usize,
        result: Proposition,
    },
    /// Like `AffineConclusion`, but carries separate interval evidence for
    /// the left and right machine expressions.  Keeping both roots explicit
    /// prevents affine cancellation from bypassing definedness checks.
    AffineConclusionWithEvidence {
        source: usize,
        left_evidence: usize,
        right_evidence: usize,
        result: Proposition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticPlan {
    pub(crate) nodes: Vec<SignedArithmeticNode>,
    pub(crate) conclusion: usize,
}

fn btree_log_work(entries: usize) -> usize {
    (usize::BITS - entries.saturating_add(1).leading_zeros()) as usize
}

fn affine_map_work(map: &BTreeMap<SignedArithmeticAtom, BigInt>) -> usize {
    let logarithmic = btree_log_work(map.len()).max(1);
    map.iter().fold(1usize, |units, (atom, coefficient)| {
        units.saturating_add(
            signed_atom_work(atom)
                .saturating_add(coefficient.bits() as usize + 1)
                .saturating_mul(logarithmic),
        )
    })
}

fn charge_affine_map_work(map: &BTreeMap<SignedArithmeticAtom, BigInt>) -> bool {
    !crate::instrumentation::deadline_exceeded_with_work(affine_map_work(map))
}

fn charge_affine_map_update_work(
    map: &BTreeMap<SignedArithmeticAtom, BigInt>,
    atom: &SignedArithmeticAtom,
    coefficient: &BigInt,
) -> bool {
    let units = signed_atom_work(atom)
        .saturating_add(coefficient.bits() as usize + 1)
        .saturating_mul(btree_log_work(map.len()).max(1))
        .saturating_mul(3);
    !crate::instrumentation::deadline_exceeded_with_work(units)
}

fn charge_bigint_binary_work(left: &BigInt, right: &BigInt) -> bool {
    let units = (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1);
    !crate::instrumentation::deadline_exceeded_with_work(units.max(1))
}

fn charge_term_work(root: &MachineTerm) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        let units = match term {
            bits32_constant!(value) => {
                (u32::BITS - constant_u32(*value).leading_zeros()) as usize + 2
            }
            MachineTerm::Variable(_) => 2,
            MachineTerm::PureFunctionApplication { name, arguments } => {
                name.len().saturating_add(arguments.len()).saturating_add(2)
            }
            binary_term!(Int32, Add, left, right)
            | binary_term!(Int32, Subtract, left, right)
            | binary_term!(Int32, Multiply, left, right)
            | binary_term!(Int32, Divide, left, right)
            | binary_term!(Int32, Remainder, left, right)
            | binary_term!(Int32, ShiftLeft, left, right)
            | binary_term!(Int32, ShiftRight, left, right)
            | binary_term!(UInt32, ShiftRight, left, right)
            | binary_term!(Int32, BitwiseAnd, left, right)
            | binary_term!(Int32, BitwiseOr, left, right)
            | binary_term!(Int32, BitwiseXor, left, right) => {
                pending.push(left);
                pending.push(right);
                3
            }
            unary_term!(Int32, BitwiseNot, operand) => {
                pending.push(operand);
                2
            }
            _ => 1,
        };
        if crate::instrumentation::deadline_exceeded_with_work(units) {
            return false;
        }
    }
    true
}

fn canonical_term_budgeted(term: &MachineTerm) -> Option<MachineTerm> {
    if !charge_term_work(term) {
        return None;
    }
    let canonical = crate::kernel::eval::canonical_term(term);
    if !charge_term_work(&canonical) {
        return None;
    }
    Some(canonical)
}

fn signed_atom_work(atom: &SignedArithmeticAtom) -> usize {
    atom.work()
}

#[cfg(test)]
fn signed_term_work(root: &MachineTerm) -> usize {
    let mut units = 0usize;
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        units = units.saturating_add(1);
        match term {
            bits32_constant!(value) => {
                units = units.saturating_add(
                    (u32::BITS - constant_u32(*value).leading_zeros()) as usize + 1,
                );
            }
            MachineTerm::Variable(_) => {}
            binary_term!(Int32, Add, left, right)
            | binary_term!(Int32, Subtract, left, right)
            | binary_term!(Int32, Multiply, left, right)
            | binary_term!(Int32, Divide, left, right)
            | binary_term!(Int32, Remainder, left, right)
            | binary_term!(Int32, ShiftLeft, left, right)
            | binary_term!(Int32, ShiftRight, left, right)
            | binary_term!(UInt32, ShiftRight, left, right)
            | binary_term!(Int32, BitwiseAnd, left, right)
            | binary_term!(Int32, BitwiseOr, left, right)
            | binary_term!(Int32, BitwiseXor, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            unary_term!(Int32, BitwiseNot, operand) => pending.push(operand),
            MachineTerm::PureFunctionApplication { name, arguments } => {
                // Function application identity compares the name and every
                // argument. Arguments are restricted to this same safe
                // machine-term fragment, so an iterative walk charges the
                // complete payload without formatting or allocating it.
                units = units.saturating_add(name.len());
                units = units.saturating_add(arguments.len());
                pending.extend(arguments.iter());
            }
            _ => {
                // Unsupported opaque payloads are rejected before they can
                // enter a checked affine claim; keep this branch bounded for
                // defensive direct callers.
            }
        }
    }
    units
}

pub(crate) fn add_claim(
    left: &SignedArithmeticClaim,
    right: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if left.carrier != right.carrier {
        return None;
    }
    if !charge_affine_map_work(&left.terms) || !charge_affine_map_work(&right.terms) {
        return None;
    }
    if !charge_bigint_binary_work(&left.constant, &right.constant) {
        return None;
    }
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        if !charge_affine_map_update_work(&terms, term, coefficient) {
            return None;
        }
        let previous = terms.get(term).cloned().unwrap_or_default();
        if !charge_bigint_binary_work(&previous, coefficient) {
            return None;
        }
        let value = previous + coefficient;
        if value.is_zero() {
            terms.remove(term);
        } else {
            terms.insert(term.clone(), value);
        }
    }
    Some(SignedArithmeticClaim {
        carrier: left.carrier,
        relation: left.relation,
        terms,
        constant: &left.constant + &right.constant,
    })
}

/// The int32 range bound of one variable atom on the given side, in the form
/// [`SignedArithmeticNode::Int32Range`] checks. The checker accepts any
/// opaque root; a planner asks only for a variable, the one atom whose
/// source spelling a printed certificate can always name.
pub(crate) fn int32_range_bound(
    atom: SignedArithmeticAtom,
    upper: bool,
) -> Option<SignedArithmeticClaim> {
    atom.as_variable()?;
    let (coefficient, constant) = if upper {
        (BigInt::one(), BigInt::from(-SIGNED_MAX))
    } else {
        (BigInt::from(-1), BigInt::from(SIGNED_MIN))
    };
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation: SignedArithmeticRelation::LessEqual,
        terms: BTreeMap::from([(atom, coefficient)]),
        constant,
    })
}

#[cfg(test)]
fn is_opaque_atom(term: &MachineTerm) -> bool {
    SignedArithmeticAtom::from_term(term).is_some_and(|atom| atom.is_opaque_root())
}

/// A signed interval operation leaves the carrier range or lacks its guard.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SignedIntervalError {
    Overflow(usize),
    InvalidOperator(usize),
}

fn interval_checked(
    lower: i128,
    upper: i128,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedIntervalError> {
    if lower < i128::from(SIGNED_MIN) || upper > i128::from(SIGNED_MAX) || lower > upper {
        return Err(SignedIntervalError::Overflow(node));
    }
    Ok(SignedArithmeticInterval {
        carrier: SignedArithmeticCarrier::SignedInt32,
        lower: lower as i64,
        upper: upper as i64,
    })
}

/// For nonnegative dividends, C remainder agrees with Euclidean remainder.
/// Translation by a constant preserves residues. An interval that crosses a
/// multiple of the divisor cannot be represented by this single interval rule.
pub(crate) fn interval_remainder_add(
    operand: &SignedArithmeticInterval,
    remainder: &SignedArithmeticInterval,
    addend: i32,
    divisor: i32,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedIntervalError> {
    if operand.carrier != SignedArithmeticCarrier::SignedInt32
        || remainder.carrier != SignedArithmeticCarrier::SignedInt32
        || divisor <= 0
        || operand.lower < 0
        || operand.upper > SIGNED_MAX
        || operand.lower > operand.upper
        || remainder.lower > remainder.upper
        || operand.lower + i64::from(addend) < 0
        || operand.upper + i64::from(addend) > SIGNED_MAX
        || remainder.lower < 0
        || remainder.upper >= i64::from(divisor)
    {
        return Err(SignedIntervalError::InvalidOperator(node));
    }
    let lower = remainder.lower + i64::from(addend);
    let upper = remainder.upper + i64::from(addend);
    let divisor = i64::from(divisor);
    if lower.div_euclid(divisor) != upper.div_euclid(divisor) {
        return Err(SignedIntervalError::InvalidOperator(node));
    }
    interval_checked(
        i128::from(lower.rem_euclid(divisor)),
        i128::from(upper.rem_euclid(divisor)),
        node,
    )
}

fn affine_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    if !matches!(condition, ConditionTerm::Compare { .. })
        && let Some(view) =
            crate::kernel::machine_integer::comparison::structural_native_comparison_view(
                condition, value,
            )
    {
        use crate::kernel::machine_integer::Relation as R;
        if view.format != MachineIntegerType::Int32
            && !(view.format == MachineIntegerType::UInt32
                && matches!(view.relation, R::Equal | R::NotEqual))
        {
            return None;
        }
        let mut terms = BTreeMap::new();
        let mut constant = BigInt::zero();
        for (operand, coefficient) in view.operands.iter().zip([BigInt::one(), -BigInt::one()]) {
            let operand = operand.operand_view();
            if let Some(value) = operand.literal().and_then(|literal| literal.as_const()) {
                let value = BigInt::from(value as i32);
                if !charge_bigint_binary_work(&coefficient, &value) {
                    return None;
                }
                let product = coefficient * value;
                if !charge_bigint_binary_work(&constant, &product) {
                    return None;
                }
                constant += product;
            } else {
                let atom = match operand {
                    crate::kernel::MachineOperandView::Shared(root) => {
                        atom_keys::from_observation(root, MachineIntegerType::Int32)?
                    }
                    crate::kernel::MachineOperandView::Legacy(value) => {
                        SignedArithmeticAtom::from_term(&canonical_term_budgeted(value)?)?
                    }
                };
                if !charge_affine_map_update_work(&terms, &atom, &coefficient) {
                    return None;
                }
                let previous = terms.get(&atom).cloned().unwrap_or_default();
                if !charge_bigint_binary_work(&previous, &coefficient) {
                    return None;
                }
                let updated = previous + coefficient;
                if updated.is_zero() {
                    terms.remove(&atom);
                } else {
                    terms.insert(atom, updated);
                }
            }
        }
        if view.relation == R::Less {
            if !charge_bigint_binary_work(&constant, &BigInt::one()) {
                return None;
            }
            constant += 1;
        }
        return Some(SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: match view.relation {
                R::Equal => SignedArithmeticRelation::Equal,
                R::NotEqual => SignedArithmeticRelation::Disequal,
                _ => SignedArithmeticRelation::LessEqual,
            },
            terms,
            constant,
        });
    }
    let widened = crate::kernel::machine_integer::comparison::narrow_comparison_as_int32(condition);
    let condition = widened.as_ref().unwrap_or(condition);
    let (relation, left, right, strict) = match (condition, value) {
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            true,
        ) => (SignedArithmeticRelation::LessEqual, left, right, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            true,
        ) => (SignedArithmeticRelation::LessEqual, left, right, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            },
            true,
        ) => (SignedArithmeticRelation::LessEqual, right, left, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        ) => (SignedArithmeticRelation::LessEqual, right, left, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            },
            false,
        ) => (SignedArithmeticRelation::LessEqual, right, left, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            },
            false,
        ) => (SignedArithmeticRelation::LessEqual, right, left, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            },
            false,
        ) => (SignedArithmeticRelation::LessEqual, left, right, false),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            false,
        ) => (SignedArithmeticRelation::LessEqual, left, right, true),
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            false,
        ) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Constant(constant), value) => {
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms: BTreeMap::new(),
                constant: if *constant == value {
                    BigInt::zero()
                } else {
                    BigInt::one()
                },
            });
        }
        _ => return None,
    };
    let (terms, mut constant) = affine_difference(left, right)?;
    if strict {
        if !charge_bigint_binary_work(&constant, &BigInt::one()) {
            return None;
        }
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

pub(crate) fn signed_arithmetic_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
    affine_claim(proposition)
}

fn affine_difference(
    left: &MachineTerm,
    right: &MachineTerm,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        match term {
            bits32_constant!(value) => {
                let value = BigInt::from(constant_u32(*value) as i32);
                if !charge_bigint_binary_work(&coefficient, &value) {
                    return None;
                }
                let product = coefficient * &value;
                if !charge_bigint_binary_work(&constant, &product) {
                    return None;
                }
                constant += product;
            }
            term => {
                let atom = canonical_term_budgeted(term)?;
                if crate::instrumentation::deadline_exceeded_with_work(
                    coefficient.bits() as usize + 1,
                ) {
                    return None;
                }
                let key = SignedArithmeticAtom::from_term(&atom)?;
                if !charge_affine_map_update_work(&terms, &key, &coefficient) {
                    return None;
                }
                let previous = terms.get(&key).cloned().unwrap_or_default();
                if !charge_bigint_binary_work(&previous, &coefficient) {
                    return None;
                }
                let updated = previous + coefficient;
                if updated.is_zero() {
                    terms.remove(&key);
                } else {
                    terms.insert(key, updated);
                }
            }
        }
    }
    Some((terms, constant))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Pointer, Variable};

    #[test]
    fn remainder_add_requires_nonnegative_bounded_dividends_and_single_residue_interval() {
        let interval = |lower, upper| SignedArithmeticInterval {
            carrier: SignedArithmeticCarrier::SignedInt32,
            lower,
            upper,
        };
        assert_eq!(
            interval_remainder_add(&interval(0, 100), &interval(2, 2), 5, 3, 0).unwrap(),
            interval(1, 1)
        );
        assert_eq!(
            interval_remainder_add(&interval(4, 100), &interval(0, 0), -1, 3, 0).unwrap(),
            interval(2, 2)
        );
        for (op, rem, add, divisor) in [
            (interval(-1, 100), interval(0, 0), 1, 2),
            (interval(0, i32::MAX as i64), interval(0, 0), 1, 2),
            (interval(0, 100), interval(0, 0), -1, 2),
            (interval(0, 100), interval(0, 0), 1, 0),
            (interval(0, 100), interval(0, 0), 1, -2),
            (interval(0, 100), interval(-1, 0), 1, 2),
            (interval(0, 100), interval(0, 2), 1, 2),
            (interval(0, 100), interval(0, 1), 1, 2),
        ] {
            assert!(interval_remainder_add(&op, &rem, add, divisor, 0).is_err());
        }
    }

    #[test]
    fn signed_read_atom_identity_survives_native_export() {
        use crate::kernel::{KernelTermExport, KernelTermImport, LoadKind, VerificationSession};
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory(crate::kernel::Memory::new());
        let address = Pointer::symbolic(Variable(997151));
        let read = |offset, kind| {
            MachineTerm::MemoryLoad(
                crate::kernel::ProgramPoint::at(&memory),
                Box::new(address.offset_by_bytes(offset)),
                kind,
            )
        };
        let scalar = read(0, LoadKind::Int32);
        let sum = MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            scalar.clone(),
            MachineTerm::constant(1),
        );
        let low_word = MachineTerm::uint32_from_64(MachineTerm::logical_machine_binary(
            MachineIntegerType::UInt64,
            MachineBinaryOp::Add,
            read(0, LoadKind::Bits64),
            MachineTerm::uint64_constant(1),
        ));
        for written in [scalar, sum, low_word] {
            let root = KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, &written)
                .unwrap();
            let shared = atom_keys::from_shared(&root).expect("shared read atom");
            let exported = KernelTermExport::machine(&root).unwrap();
            assert_eq!(SignedArithmeticAtom::from_term(&exported), Some(shared));
        }
        assert_ne!(
            SignedArithmeticAtom::from_term(&read(0, LoadKind::Int32)),
            SignedArithmeticAtom::from_term(&read(4, LoadKind::Int32)),
        );
        assert_ne!(
            SignedArithmeticAtom::from_term(&read(0, LoadKind::Int32)),
            SignedArithmeticAtom::from_term(&read(0, LoadKind::UInt32)),
        );
    }

    fn x() -> MachineTerm {
        MachineTerm::Variable(Variable(1))
    }

    #[test]
    fn narrowed_native_variable_is_an_opaque_distinct_signed_atom() {
        let variable = MachineTerm::Variable(Variable(42));
        let narrowed = MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(variable.clone()),
        );
        assert!(is_opaque_atom(&narrowed));
        assert_ne!(
            SignedArithmeticAtom::from_term(&narrowed),
            SignedArithmeticAtom::from_term(&variable)
        );
        let changed = MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(MachineTerm::Variable(Variable(43))),
        );
        assert_ne!(
            SignedArithmeticAtom::from_term(&narrowed),
            SignedArithmeticAtom::from_term(&changed)
        );
        let computed = MachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(variable),
                right: Box::new(MachineTerm::uint64_constant(2)),
            }),
        );
        assert!(is_opaque_atom(&computed));
        assert_ne!(
            SignedArithmeticAtom::from_term(&computed),
            SignedArithmeticAtom::from_term(&narrowed)
        );
        assert_eq!(
            SignedArithmeticAtom::from_term(&narrowed).unwrap().work(),
            1
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/signed_arithmetic/tests.rs");
    }
}

#[cfg(test)]
mod narrowed_expression_tests {
    use super::*;

    #[test]
    fn narrowed_native_expression_atom_preserves_structure_and_width() {
        let n = MachineTerm::Variable(Variable(100));
        let native = MachineTerm::uint64_subtract(
            n.clone(),
            MachineTerm::uint64_remainder(n.clone(), MachineTerm::uint64_constant(4)),
        );
        let narrow = MachineTerm::uint32_from_64(native);
        assert!(is_opaque_atom(&narrow));
        let other = MachineTerm::uint32_from_64(MachineTerm::uint64_subtract(
            n.clone(),
            MachineTerm::uint64_remainder(n.clone(), MachineTerm::uint64_constant(3)),
        ));
        assert_ne!(
            SignedArithmeticAtom::from_term(&narrow),
            SignedArithmeticAtom::from_term(&other)
        );
        assert_ne!(
            SignedArithmeticAtom::from_term(&narrow),
            SignedArithmeticAtom::from_term(&n)
        );
        let unsupported =
            MachineTerm::uint32_from_64(MachineTerm::int64_add(n, MachineTerm::int64_constant(1)));
        assert!(SignedArithmeticAtom::from_term(&unsupported).is_none());
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/signed_arithmetic/narrowed_expression_tests.rs");
    }
}

#[cfg(test)]
mod format_tests {
    use super::*;
    use crate::kernel::Variable;

    /// The signed fragment reads `int32` operators and a word's logical
    /// right shift, never a `uint32` sign-free operator, whose value it
    /// would read as an `int32` one (decision G7).
    #[test]
    fn the_signed_fragment_refuses_a_uint32_sign_free_operator() {
        let operand = || Box::new(MachineTerm::Variable(Variable(186_001)));
        assert!(signed_binary(&binary_node!(Int32, Add, operand(), operand())).is_some());
        assert!(signed_binary(&binary_node!(Int32, Divide, operand(), operand())).is_some());
        assert!(signed_binary(&binary_node!(UInt32, ShiftRight, operand(), operand())).is_some());
        for node in [
            binary_node!(UInt32, Add, operand(), operand()),
            binary_node!(UInt32, Multiply, operand(), operand()),
            binary_node!(UInt32, Divide, operand(), operand()),
            binary_node!(UInt32, Remainder, operand(), operand()),
        ] {
            assert!(signed_binary(&node).is_none(), "{node:?}");
        }
    }
}
