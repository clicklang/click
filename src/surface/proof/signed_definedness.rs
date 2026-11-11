//! Smart closure of an `int32` or `int64` definedness goal from the
//! operands' bounds.
//!
//! `defined(a + b)` and `defined(a - b)` over `int32` or `int64` lower to the
//! conjunction of ordinary exact-result range bounds. The checked
//! `int32_defined` / `int64_defined` rule of the `rules` arithmetic
//! certificate family establishes it from each operand's width range and
//! cited constant bounds. This closer only selects those bounds: the constant
//! order and equality facts of the goal's width indexed under each operand
//! term, or, for `solve() using`, the listed premises that bound an operand.
//! It spells each cited fact through the goal's own operand spelling, so the
//! certificate re-lowers to exactly the facts it names. Selection is a keyed
//! lookup per operand and never scans the context; the kernel checker, not
//! this selector, decides whether the ranges exclude overflow. Both widths
//! share every line of this selection; the width only chooses which index
//! and comparison family the lookups read.

use super::surface_synthesis::synthesize_surface_machine_expression;
use super::*;
use crate::kernel::SignedDefinedWidth;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::proof::arithmetic_special::{
    signed_definedness_operands, signed_width_constant,
};
use crate::kernel::{CompareRelation, MachineIntegerType};

impl<'a> Proof<'a> {
    fn synthesize_machine_term_here(&self, term: &MachineTerm) -> Option<ContractExpression> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => synthesize_surface_machine_expression(
                term,
                context.parameter_binding,
                context.fixed_state.state,
            ),
            ProofContext::Execution(_) => {
                let view = self.premise_fixed_state_view()?;
                synthesize_surface_machine_expression(
                    term,
                    view.parameter_binding,
                    view.fixed_state.state,
                )
            }
        }
    }

    fn signed_definedness_surface_operands(
        &self,
    ) -> Option<(&ContractExpression, &ContractExpression)> {
        let ClickProposition::Defined { expression } = self.surface_goal()? else {
            return None;
        };
        match expression {
            ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) => {
                Some((left.as_ref(), right.as_ref()))
            }
            _ => None,
        }
    }
}

/// Spell one constant bound fact of `width` on `term` with `term`'s spelling
/// from the goal, in the fact's own orientation and polarity.
fn spell_signed_bound(
    width: SignedDefinedWidth,
    fact: &Proposition,
    term: &MachineTerm,
    surface: &ContractExpression,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(condition, value) = fact else {
        return None;
    };
    use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
    let view = comparison_view(condition, true)?;
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    if view.format != format
        && !(format == MachineIntegerType::Int32
            && view.format == MachineIntegerType::UInt32
            && matches!(view.relation, Relation::Equal | Relation::NotEqual))
    {
        return None;
    }
    let operator = match view.relation {
        Relation::Equal => ComparisonOperator::Equal,
        Relation::NotEqual => ComparisonOperator::NotEqual,
        Relation::Less => ComparisonOperator::LessThan,
        Relation::LessEqual => ComparisonOperator::LessEqual,
    };
    let expected = crate::kernel::SharedMachineIntegerTerm::intern(format, term.clone());
    let side = |side: crate::kernel::MachineOperandView<'_>| {
        if side.retain(format) == expected {
            Some(surface.clone())
        } else {
            let number = match width {
                SignedDefinedWidth::Int32 => {
                    side.word32_constant().map(|bits| i64::from(bits as i32))
                }
                SignedDefinedWidth::Int64 => side.int64_constant(),
            };
            number.map(signed_literal)
        }
    };
    let [left, right] = view
        .operands
        .each_ref()
        .map(|operand| operand.operand_view());
    let comparison = ClickProposition::Comparison {
        left: side(left)?,
        operator,
        right: side(right)?,
    };
    Some(if *value {
        comparison
    } else {
        ClickProposition::Not(Box::new(comparison))
    })
}

fn signed_literal(value: i64) -> ContractExpression {
    let magnitude = ContractExpression::IntegerLiteral(value.unsigned_abs().to_string());
    if value < 0 {
        ContractExpression::Negate(Box::new(magnitude))
    } else {
        magnitude
    }
}

/// The constant an exact equality fact of `width` fixes `term` to.
fn exact_constant_of(
    width: SignedDefinedWidth,
    fact: &Proposition,
    term: &MachineTerm,
) -> Option<i64> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = fact
    else {
        return None;
    };
    if left.as_ref() == term {
        signed_width_constant(width, right)
    } else if right.as_ref() == term {
        signed_width_constant(width, left)
    } else {
        None
    }
}

/// `term` with each summand of its sums and differences that `constant`
/// fixes to zero removed, or `None` when no summand is removed.
fn substitute_constant_summands(
    width: SignedDefinedWidth,
    term: &MachineTerm,
    constant: &dyn Fn(&MachineTerm) -> Option<i64>,
) -> Option<MachineTerm> {
    let zero = |summand: &MachineTerm| {
        signed_width_constant(width, summand).is_none() && constant(summand) == Some(0)
    };
    match term {
        binary_term!(Int32, Add, left, right) => {
            if zero(left) {
                return Some(
                    substitute_constant_summands(width, right, constant)
                        .unwrap_or_else(|| right.as_ref().clone()),
                );
            }
            if zero(right) {
                return Some(
                    substitute_constant_summands(width, left, constant)
                        .unwrap_or_else(|| left.as_ref().clone()),
                );
            }
            let new_left = substitute_constant_summands(width, left, constant);
            let new_right = substitute_constant_summands(width, right, constant);
            (new_left.is_some() || new_right.is_some()).then(|| {
                binary_node!(
                    Int32,
                    Add,
                    Box::new(new_left.unwrap_or_else(|| left.as_ref().clone())),
                    Box::new(new_right.unwrap_or_else(|| right.as_ref().clone())),
                )
            })
        }
        binary_term!(Int32, Subtract, left, right) => {
            if zero(right) {
                return Some(
                    substitute_constant_summands(width, left, constant)
                        .unwrap_or_else(|| left.as_ref().clone()),
                );
            }
            let new_left = substitute_constant_summands(width, left, constant)?;
            Some(binary_node!(
                Int32,
                Subtract,
                Box::new(new_left),
                right.clone()
            ))
        }
        _ => None,
    }
}

/// The overflow conjuncts of a definedness conjunction whose operation is
/// not itself an operand of another conjunct: the candidates for the
/// written expression's outermost operation.
fn outermost_overflow_conjuncts(
    goal: &Proposition,
) -> Vec<(SignedDefinedWidth, &MachineTerm, &MachineTerm)> {
    fn collect<'a>(
        proposition: &'a Proposition,
        out: &mut Vec<(SignedDefinedWidth, &'a MachineTerm, &'a MachineTerm, bool)>,
    ) {
        match proposition {
            Proposition::And(left, right) => {
                collect(left, out);
                collect(right, out);
            }
            other => out.extend(signed_definedness_operands(other)),
        }
    }
    let Proposition::And(_, _) = goal else {
        return Vec::new();
    };
    let mut conjuncts = Vec::new();
    collect(goal, &mut conjuncts);
    let operation = |left: &MachineTerm, right: &MachineTerm, subtract: bool| {
        let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
        if subtract {
            binary_node!(Int32, Subtract, left, right)
        } else {
            binary_node!(Int32, Add, left, right)
        }
    };
    conjuncts
        .iter()
        .filter(|(_, left, right, subtract)| {
            let term = operation(left, right, *subtract);
            !conjuncts.iter().any(|(_, other_left, other_right, _)| {
                **other_left == term || **other_right == term
            })
        })
        .map(|(width, left, right, _)| (*width, *left, *right))
        .collect()
}

mod search;
