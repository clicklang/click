//! `arithmetic() using { ... }` on a linear `uint64` or `int64` order or
//! equality goal, or a linear `uint32` order goal, the certificate families
//! miss.
//!
//! A 64-bit goal is proved through its exact Integer observations, by the
//! steps a proof would write by hand: each listed 64-bit order premise is
//! restated over its observations by `known`, each sum or difference in
//! the premises and the goal is shown to stay in range (an unsigned one does
//! not wrap, a signed one is defined) and then observed term by term by its
//! in-range identity, the Integer claim is composed with ordinary library
//! laws, and `known` concludes the goal. Known checks intrinsic type ranges
//! and the exact operation identities from their two stated bounds. The
//! checked steps are retained directly for expansion.
use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::{bits32_constant, int64_constant, uint64_constant};

/// Which integers a goal orders: the 64-bit ones, or `uint32`, whose order
/// this route reads only for an order goal ([`Carrier::of_order_goal`]).
#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum Carrier {
    UInt64,
    Int64,
    UInt32,
}

impl Carrier {
    /// [`Carrier::of`], and a `uint32` order: the goals and premises an
    /// `arithmetic() using` order bridge reads.
    fn of_order_goal(proposition: &Proposition) -> Option<Self> {
        Self::of(proposition).or_else(|| {
            matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(
                    _,
                    _,
                ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare {
                        format: MachineIntegerType::UInt32,
                        relation: CompareRelation::LessThan
                            | CompareRelation::LessEqual
                            | CompareRelation::GreaterThan
                            | CompareRelation::GreaterEqual,
                        ..
                    }, _))))
            .then_some(Self::UInt32)
        })
    }

    pub(super) fn of(proposition: &Proposition) -> Option<Self> {
        match proposition {
            condition_source_0 @ Proposition::ConditionIs(_, _)
                if let Some((
                    ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessEqual,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::GreaterEqual,
                        ..
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                Some(Self::UInt64)
            }
            condition_source_0 @ Proposition::ConditionIs(_, _)
                if let Some((
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::LessThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::LessEqual,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::GreaterThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::GreaterEqual,
                        ..
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                Some(Self::Int64)
            }
            _ => None,
        }
    }

    pub(super) fn name(self) -> &'static str {
        match self {
            Self::UInt64 => "uint64",
            Self::Int64 => "int64",
            Self::UInt32 => "uint32",
        }
    }

    /// Preserve the comparison's implicit promotion when emitting arguments
    /// for a bridge whose binders explicitly require a 64-bit value.
    pub(super) fn typed_literals(self, expression: &SurfaceTerm) -> SurfaceTerm {
        match expression {
            SurfaceTerm::IntegerLiteral(text) => {
                let value = match self {
                    Self::UInt64 => text
                        .parse::<u64>()
                        .ok()
                        .map(|value| ProgramValue::UInt64(MachineTerm::uint64_constant(value))),
                    Self::Int64 => text
                        .parse::<i64>()
                        .ok()
                        .map(|value| ProgramValue::Int64(MachineTerm::int64_constant(value))),
                    Self::UInt32 => text
                        .parse::<u32>()
                        .ok()
                        .map(|value| ProgramValue::UInt32(MachineTerm::uint32_constant(value))),
                };
                value
                    .map(|value| SurfaceTerm::ProgramExpression(ProgramExpression::Value(value)))
                    .unwrap_or_else(|| expression.clone())
            }
            SurfaceTerm::Add(left, right) => SurfaceTerm::Add(
                Box::new(self.typed_literals(left)),
                Box::new(self.typed_literals(right)),
            ),
            SurfaceTerm::Subtract(left, right) => SurfaceTerm::Subtract(
                Box::new(self.typed_literals(left)),
                Box::new(self.typed_literals(right)),
            ),
            SurfaceTerm::At {
                selector,
                expression,
            } => {
                let read = at_operand(selector, expression);
                if matches!(read, SurfaceTerm::At { .. }) {
                    read
                } else {
                    self.typed_literals(&read)
                }
            }
            _ => expression.clone(),
        }
    }

    /// The bridge theorem `<type>_<stem>`.
    /// The machine format a goal of this carrier orders.
    pub(super) fn machine_type(self) -> crate::kernel::MachineIntegerType {
        match self {
            Self::UInt64 => crate::kernel::MachineIntegerType::UInt64,
            Self::Int64 => crate::kernel::MachineIntegerType::Int64,
            Self::UInt32 => crate::kernel::MachineIntegerType::UInt32,
        }
    }

    /// The type's range, as Integer literals.
    fn range(self) -> (String, String) {
        let (minimum, maximum) = crate::kernel::machine_integer::range::range(self.machine_type());
        (minimum.to_string(), maximum.to_string())
    }
}

/// How a premise or a goal relates its two sides.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Relation {
    Less,
    LessEqual,
    Equal,
}

/// `left < right`, `left <= right` or `left == right`, as the bridges state
/// them. A comparison written the other way round is read with its sides
/// exchanged, and so is a negated order: `not a < b` is `b <= a`, which
/// holds of every pair of values of one integer type. The last part says
/// whether the proposition is written in the bridge's own form.
pub(super) fn relation_parts(
    proposition: &SurfaceProposition,
) -> Option<(SurfaceTerm, SurfaceTerm, Relation, bool)> {
    if let SurfaceProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (lower, upper, relation, forward) = relation_parts(proposition)?;
        return Some((
            at_operand(selector, &lower),
            at_operand(selector, &upper),
            relation,
            forward,
        ));
    }
    let (proposition, negated) = match proposition {
        SurfaceProposition::Not(body) => (body.as_ref(), true),
        other => (other, false),
    };
    let SurfaceProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let (lower, upper, relation, written_forward) = match (operator, negated) {
        (ComparisonOperator::LessThan, false) => (left, right, Relation::Less, true),
        (ComparisonOperator::LessEqual, false) => (left, right, Relation::LessEqual, true),
        (ComparisonOperator::GreaterThan, false) => (right, left, Relation::Less, false),
        (ComparisonOperator::GreaterEqual, false) => (right, left, Relation::LessEqual, false),
        (ComparisonOperator::Equal, false) => (left, right, Relation::Equal, true),
        (ComparisonOperator::LessThan, true) => (right, left, Relation::LessEqual, false),
        (ComparisonOperator::LessEqual, true) => (right, left, Relation::Less, false),
        (ComparisonOperator::GreaterThan, true) => (left, right, Relation::LessEqual, false),
        (ComparisonOperator::GreaterEqual, true) => (left, right, Relation::Less, false),
        _ => return None,
    };
    Some((lower.clone(), upper.clone(), relation, written_forward))
}

/// [`relation_parts`] for a comparison the kernel holds natively. One of
/// exact observations, `to_integer(a) <= to_integer(b)`, is that native
/// comparison of `a` and `b`, and is read as it.
fn native_relation_parts(
    proposition: &SurfaceProposition,
) -> Option<(SurfaceTerm, SurfaceTerm, Relation, bool)> {
    let (lower, upper, relation, forward) = relation_parts(proposition)?;
    if let (Some(lower), Some(upper)) = (observed(&lower), observed(&upper)) {
        return Some((lower, upper, relation, forward));
    }
    Some((lower, upper, relation, forward))
}

/// The machine expression `expression` observes, when it is `to_integer(e)`.
fn observed(expression: &SurfaceTerm) -> Option<SurfaceTerm> {
    match expression {
        SurfaceTerm::Call { name, arguments } if name == "to_integer" => {
            match arguments.as_slice() {
                [argument] => Some(argument.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether `proposition` compares two exact observations.
pub(super) fn compares_observations(proposition: &SurfaceProposition) -> bool {
    let proposition = match proposition {
        SurfaceProposition::Not(body) => body.as_ref(),
        other => other,
    };
    matches!(proposition, SurfaceProposition::Comparison { left, right, .. }
        if observed(left).is_some() && observed(right).is_some())
}

/// Read linear arithmetic in its named state. Constants are independent
/// of memory; each other operand retains the selector checked by lowering.
fn at_operand(selector: &ProgramPointSelector, expression: &SurfaceTerm) -> SurfaceTerm {
    match expression {
        SurfaceTerm::IntegerLiteral(_)
        | SurfaceTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt64(uint64_constant!(_))
            | ProgramValue::Int64(int64_constant!(_))
            | ProgramValue::UInt32(bits32_constant!(_)),
        ))
        | SurfaceTerm::At { .. }
        | SurfaceTerm::Old(_) => expression.clone(),
        SurfaceTerm::Add(left, right) => SurfaceTerm::Add(
            Box::new(at_operand(selector, left)),
            Box::new(at_operand(selector, right)),
        ),
        SurfaceTerm::Subtract(left, right) => SurfaceTerm::Subtract(
            Box::new(at_operand(selector, left)),
            Box::new(at_operand(selector, right)),
        ),
        _ => SurfaceTerm::At {
            selector: selector.clone(),
            expression: Box::new(expression.clone()),
        },
    }
}

pub(super) fn relate(
    lower: SurfaceTerm,
    upper: SurfaceTerm,
    relation: Relation,
) -> SurfaceProposition {
    SurfaceProposition::Comparison {
        left: lower,
        operator: match relation {
            Relation::Less => ComparisonOperator::LessThan,
            Relation::LessEqual => ComparisonOperator::LessEqual,
            Relation::Equal => ComparisonOperator::Equal,
        },
        right: upper,
    }
}

fn order(lower: SurfaceTerm, upper: SurfaceTerm, strict: bool) -> SurfaceProposition {
    relate(
        lower,
        upper,
        if strict {
            Relation::Less
        } else {
            Relation::LessEqual
        },
    )
}

/// The exact Integer observation of a `uint64` expression. A literal is
/// written as the Integer it is: the Integer certificate reads a premise as
/// it is spelled, and `to_integer(2u64)` spelled out is an atom to it.
pub(super) fn to_integer(expression: &SurfaceTerm) -> SurfaceTerm {
    // A value read at a state is observed there: `at(s, to_integer(i))`.
    // A literal is the same at every state.
    if let SurfaceTerm::At {
        selector,
        expression,
    } = expression
    {
        return match to_integer(expression) {
            literal @ SurfaceTerm::IntegerLiteral(_) => literal,
            observed => SurfaceTerm::At {
                selector: selector.clone(),
                expression: Box::new(observed),
            },
        };
    }
    if let SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(value))) =
        expression
        && let Some(constant) = value.uint64_as_const()
    {
        return SurfaceTerm::IntegerLiteral(constant.to_string());
    }
    if let SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int64(value))) =
        expression
        && let Some(constant) = value.int64_as_const()
    {
        return SurfaceTerm::IntegerLiteral(constant.to_string());
    }
    if let SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt32(value))) =
        expression
        && let Some(constant) = value.as_const()
    {
        return SurfaceTerm::IntegerLiteral(constant.to_string());
    }
    SurfaceTerm::Call {
        name: "to_integer".to_string(),
        arguments: vec![expression.clone()],
    }
}

/// The sums and differences inside `expression`, innermost first.
fn collect_operations(expression: &SurfaceTerm, operations: &mut Vec<SurfaceTerm>) {
    if let SurfaceTerm::Add(left, right) | SurfaceTerm::Subtract(left, right) = expression {
        collect_operations(left, operations);
        collect_operations(right, operations);
        if !operations.contains(expression) {
            operations.push(expression.clone());
        }
    }
}

/// The operands of the sums and differences in `expression` that are not
/// themselves one, and are not literals: the values whose type range the
/// Integer claim may need.
fn collect_atoms(expression: &SurfaceTerm, atoms: &mut Vec<SurfaceTerm>) {
    match expression {
        SurfaceTerm::Add(left, right) | SurfaceTerm::Subtract(left, right) => {
            collect_atoms(left, atoms);
            collect_atoms(right, atoms);
        }
        SurfaceTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt64(value) | ProgramValue::Int64(value),
        )) if value.uint64_as_const().is_some() || value.int64_as_const().is_some() => {}
        SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt32(value)))
            if value.as_const().is_some() => {}
        atom => {
            if !atoms.contains(atom) {
                atoms.push(atom.clone());
            }
        }
    }
}

/// Whether `expression` is a linear side: a sum or difference, or a plain
/// operand. A side that is itself a product, a quotient, a shift or a mask
/// is not a linear claim, and an equality over one is left to the families
/// that read those operations. Such an operation inside a sum is an operand
/// like any other: `(n - n % 4u64) - r` is linear in `n`, `n % 4u64` and `r`.
fn linear(expression: &SurfaceTerm) -> bool {
    !matches!(
        expression,
        SurfaceTerm::Multiply(..)
            | SurfaceTerm::Divide(..)
            | SurfaceTerm::Remainder(..)
            | SurfaceTerm::ShiftLeft(..)
            | SurfaceTerm::RustShiftLeft(..)
            | SurfaceTerm::ShiftRight(..)
            | SurfaceTerm::RustShiftRight(..)
            | SurfaceTerm::BitwiseAnd(..)
            | SurfaceTerm::BitwiseOr(..)
            | SurfaceTerm::BitwiseXor(..)
            | SurfaceTerm::BitwiseNot(..)
            | SurfaceTerm::Negate(..)
            | SurfaceTerm::CUnary { .. }
            | SurfaceTerm::MemoryLoad { .. }
            | SurfaceTerm::If { .. }
    )
}

/// The 64-bit type a literal written in `expression` has, if one is.
fn literal_carrier(expression: &SurfaceTerm) -> Option<Carrier> {
    match expression {
        SurfaceTerm::Add(left, right) | SurfaceTerm::Subtract(left, right) => {
            literal_carrier(left).or_else(|| literal_carrier(right))
        }
        SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(_))) => {
            Some(Carrier::UInt64)
        }
        SurfaceTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int64(_))) => {
            Some(Carrier::Int64)
        }
        _ => None,
    }
}

pub(super) fn have(proposition: SurfaceProposition, proof: Vec<ProofStep>) -> ProofStep {
    ProofStep::Have {
        proposition,
        proof: Box::new(ProofCertificate::from_validated_steps(proof)),
    }
}

/// Check the observed machine value's intrinsic type range.
pub(super) fn type_range(_bound: SurfaceProposition) -> ProofStep {
    ProofStep::Known
}

/// Check the machine identity after its two exact-result bounds were proved.
pub(super) fn operation_identity(
    _lower: SurfaceProposition,
    _upper: SurfaceProposition,
    _identity: SurfaceProposition,
) -> ProofStep {
    ProofStep::Known
}

thread_local! {
    static BRIDGING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Marks the bridge's own steps. Its Integer claims have crossed the bridge:
/// the observed goal, `to_integer(a) < to_integer(b)`, reads as the native
/// goal it came from and would otherwise be bridged again.
struct BridgeScope;

impl BridgeScope {
    fn enter() -> Option<Self> {
        // Built only when entered: a guard built and dropped on a nested
        // entry would clear the flag the outer one holds.
        if BRIDGING.with(|bridging| bridging.replace(true)) {
            None
        } else {
            Some(BridgeScope)
        }
    }
}

impl Drop for BridgeScope {
    fn drop(&mut self) {
        BRIDGING.with(|bridging| bridging.set(false));
    }
}

impl<'a> Proof<'a> {}

// Discovery methods are deliberately not methods of Proof.

// Source spelling adapters for the kernel ProofSearch interface.
mod search;
