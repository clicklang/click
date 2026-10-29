use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::MachineIntegerType;
use crate::kernel::binary_node;
use crate::kernel::{binary_term, unary_term};
#[cfg(test)]
use crate::surface::planning::solve::{
    SolveEvidence, plan_explicit_equality_rewrites_from, plan_solve_certificate,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum NormalizedProposition {
    True,
    False,
    Proposition(Proposition),
}

pub(in crate::surface) fn normalize_proposition(
    proposition: &Proposition,
) -> NormalizedProposition {
    match proposition {
        Proposition::Equal(left, right) => match normalized_terms_equal(left, right) {
            Some(true) => NormalizedProposition::True,
            Some(false) => NormalizedProposition::False,
            None => NormalizedProposition::Proposition(Proposition::Equal(
                normalize_term(left),
                normalize_term(right),
            )),
        },
        Proposition::ConditionIs(condition, expected) => {
            match normalize_condition_without_assumptions(condition) {
                Some(actual) if actual == *expected => NormalizedProposition::True,
                Some(_) => NormalizedProposition::False,
                None => NormalizedProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (NormalizedProposition::False, _) | (_, NormalizedProposition::False) => {
                    NormalizedProposition::False
                }
                (NormalizedProposition::True, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::True, right) => right,
                (left, NormalizedProposition::True) => left,
                (left, right) => NormalizedProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (NormalizedProposition::True, _) | (_, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::False, NormalizedProposition::False) => {
                    NormalizedProposition::False
                }
                (NormalizedProposition::False, right) => right,
                (left, NormalizedProposition::False) => left,
                (left, right) => NormalizedProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match normalize_proposition(body) {
            NormalizedProposition::True => NormalizedProposition::False,
            NormalizedProposition::False => NormalizedProposition::True,
            body => NormalizedProposition::Proposition(Proposition::Not(Box::new(
                body.into_proposition(),
            ))),
        },
        Proposition::Implies(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (NormalizedProposition::False, _) | (_, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::True, right) => right,
                (_, NormalizedProposition::False) => NormalizedProposition::False,
                (left, right) => NormalizedProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        _ => NormalizedProposition::Proposition(proposition.clone()),
    }
}

pub(in crate::surface) use crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality;

#[cfg(test)]
fn check_solve_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
    certificate: &SolveEvidence,
) -> bool {
    match certificate {
        SolveEvidence::Normalize => {
            matches!(
                normalize_proposition(proposition),
                NormalizedProposition::True
            )
        }
        SolveEvidence::Derivation(derivation) => {
            derivation.conclusion() == proposition && derivation.check(assumptions)
        }
    }
}

#[cfg(test)]
pub(in crate::surface) fn solve_proposition(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> NormalizedProposition {
    if let Some(certificate) = plan_solve_certificate(proposition, assumptions)
        && check_solve_certificate(proposition, assumptions, &certificate)
    {
        return NormalizedProposition::True;
    }
    let simplified = match proposition {
        Proposition::Equal(left, right) => match normalized_terms_equal(left, right) {
            Some(true) => NormalizedProposition::True,
            Some(false) => NormalizedProposition::False,
            None => NormalizedProposition::Proposition(Proposition::Equal(
                normalize_term(left),
                normalize_term(right),
            )),
        },
        Proposition::ConditionIs(condition, expected) => {
            match normalize_condition(condition, assumptions) {
                Some(actual) if actual == *expected => NormalizedProposition::True,
                Some(_) => NormalizedProposition::False,
                None => NormalizedProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = solve_proposition(left, assumptions);
            let right = solve_proposition(right, assumptions);
            match (left, right) {
                (NormalizedProposition::False, _) | (_, NormalizedProposition::False) => {
                    NormalizedProposition::False
                }
                (NormalizedProposition::True, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::True, right) => right,
                (left, NormalizedProposition::True) => left,
                (left, right) => NormalizedProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = solve_proposition(left, assumptions);
            let right = solve_proposition(right, assumptions);
            match (left, right) {
                (NormalizedProposition::True, _) | (_, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::False, NormalizedProposition::False) => {
                    NormalizedProposition::False
                }
                (NormalizedProposition::False, right) => right,
                (left, NormalizedProposition::False) => left,
                (left, right) => NormalizedProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match solve_proposition(body, assumptions) {
            NormalizedProposition::True => NormalizedProposition::False,
            NormalizedProposition::False => NormalizedProposition::True,
            body => NormalizedProposition::Proposition(Proposition::Not(Box::new(
                body.into_proposition(),
            ))),
        },
        Proposition::Implies(left, right) => {
            let left = solve_proposition(left, assumptions);
            let right = solve_proposition(right, assumptions);
            match (left, right) {
                (NormalizedProposition::False, _) | (_, NormalizedProposition::True) => {
                    NormalizedProposition::True
                }
                (NormalizedProposition::True, right) => right,
                (_, NormalizedProposition::False) => NormalizedProposition::False,
                (left, right) => NormalizedProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::ForAll { .. }
        | Proposition::Exists { .. }
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CConditionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CStatementVerifies { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionVerifies { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CFunctionPartiallySatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryReadDefined { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceComposition(_)
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CHeapAllocationFreed { .. } => {
            NormalizedProposition::Proposition(proposition.clone())
        }
    };
    if matches!(simplified, NormalizedProposition::True) {
        // A successful smart tactic must come from the certificate path above.
        NormalizedProposition::Proposition(proposition.clone())
    } else {
        simplified
    }
}

impl NormalizedProposition {
    fn into_proposition(self) -> Proposition {
        match self {
            Self::True => Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            Self::False => Proposition::ConditionIs(ConditionTerm::Constant(false), true),
            Self::Proposition(proposition) => proposition,
        }
    }
}

pub(in crate::surface) fn normalized_terms_equal(left: &Term, right: &Term) -> Option<bool> {
    let left = normalize_term(left);
    let right = normalize_term(right);
    if left == right {
        return Some(true);
    }
    match (&left, &right) {
        (Term::Bitvector32(left), Term::Bitvector32(right)) => Some(
            evaluate_bitvector_constant(&normalize_bitvector(left))?
                == evaluate_bitvector_constant(&normalize_bitvector(right))?,
        ),
        (Term::Condition(left), Term::Condition(right)) => Some(
            normalize_condition_without_assumptions(left)?
                == normalize_condition_without_assumptions(right)?,
        ),
        _ => None,
    }
}

pub(in crate::surface) fn normalize_term(term: &Term) -> Term {
    match term {
        Term::CValue(value @ CValue::PointerInteger(_)) => {
            normalize_term(&Term::CValue(value.numeric_value().clone()))
        }
        Term::Condition(condition) => match normalize_condition_without_assumptions(condition) {
            Some(value) => Term::Condition(ConditionTerm::Constant(value)),
            None => term.clone(),
        },
        Term::Bitvector32(term) => Term::Bitvector32(normalize_bitvector(term)),
        Term::CValue(CValue::Int32(term)) => Term::CValue(CValue::Int32(normalize_bitvector(term))),
        Term::CValue(CValue::Int64(term)) => Term::CValue(CValue::Int64(normalize_bitvector(term))),
        Term::CValue(CValue::UInt64(term)) => {
            Term::CValue(CValue::UInt64(normalize_bitvector(term)))
        }
        _ => term.clone(),
    }
}

#[cfg(test)]
pub(in crate::surface) fn normalize_condition(
    condition: &ConditionTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    normalize_condition_without_assumptions(condition).or_else(|| {
        assumptions
            .selected_for_test()
            .decide_selected_condition(condition)
    })
}

pub(in crate::surface) fn normalize_condition_without_assumptions(
    condition: &ConditionTerm,
) -> Option<bool> {
    match condition {
        ConditionTerm::PointerValueEqual(_, _) => {
            crate::kernel::SelectedFacts::from_propositions(&[]).decide_selected_condition(condition)
        }

        ConditionTerm::AlgebraicEqual(_, _) => {
            crate::kernel::SelectedFacts::from_propositions(&[]).decide_selected_condition(condition)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            if left == right {
                Some(true)
            } else {
                Some(left.as_const()? == right.as_const()?)
            }
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            if left == right {
                Some(false)
            } else {
                Some(left.as_const()? != right.as_const()?)
            }
        }
        ConditionTerm::IntegerLessThan(left, right) => Some(left.as_const()? < right.as_const()?),
        ConditionTerm::IntegerLessEqual(left, right) => Some(left.as_const()? <= right.as_const()?),
        ConditionTerm::IntegerGreaterThan(left, right) => {
            Some(left.as_const()? > right.as_const()?)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            Some(left.as_const()? >= right.as_const()?)
        }
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(evaluate_bitvector_constant(&left)? == evaluate_bitvector_constant(&right)?)
            }
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessThan, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((evaluate_bitvector_constant(&left)? as i32) < (evaluate_bitvector_constant(&right)? as i32))
            }
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::LessEqual, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (evaluate_bitvector_constant(&left)? as i32) <= (evaluate_bitvector_constant(&right)? as i32),
                )
            }
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::GreaterThan, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((evaluate_bitvector_constant(&left)? as i32) > (evaluate_bitvector_constant(&right)? as i32))
            }
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int32, relation: CompareRelation::GreaterEqual, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (evaluate_bitvector_constant(&left)? as i32) >= (evaluate_bitvector_constant(&right)? as i32),
                )
            }
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::LessThan, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(false);
            }
            Some(left.int64_as_const()? < right.int64_as_const()?)
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::LessEqual, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(true);
            }
            Some(left.int64_as_const()? <= right.int64_as_const()?)
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::GreaterThan, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(false);
            }
            Some(left.int64_as_const()? > right.int64_as_const()?)
        }
        ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::GreaterEqual, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(true);
            }
            Some(left.int64_as_const()? >= right.int64_as_const()?)
        }
        ConditionTerm::Compare { format: MachineIntegerType::UInt64, relation: CompareRelation::LessThan, left, right } => Some({
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(false);
            }
            left.uint64_as_const()? < right.uint64_as_const()?
        }),
        ConditionTerm::Compare { format: MachineIntegerType::UInt64, relation: CompareRelation::LessEqual, left, right } => Some({
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(true);
            }
            left.uint64_as_const()? <= right.uint64_as_const()?
        }),
        ConditionTerm::Compare { format: MachineIntegerType::UInt64, relation: CompareRelation::GreaterThan, left, right } => Some({
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(false);
            }
            left.uint64_as_const()? > right.uint64_as_const()?
        }),
        ConditionTerm::Compare { format: MachineIntegerType::UInt64, relation: CompareRelation::GreaterEqual, left, right } => Some({
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(true);
            }
            left.uint64_as_const()? >= right.uint64_as_const()?
        }),
        ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, left, right } => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            if left == right {
                return Some(true);
            }
            let left = left
                .int64_as_const()
                .map(|value| value as u64)
                .or_else(|| left.uint64_as_const())?;
            let right = right
                .int64_as_const()
                .map(|value| value as u64)
                .or_else(|| right.uint64_as_const())?;
            Some(left == right)
        }
        ConditionTerm::Variable(_)
        // The other formats have no constant folding here.
        | ConditionTerm::Compare { .. }
        | ConditionTerm::Overflows { .. }
        | ConditionTerm::Float32(_)
        | ConditionTerm::Float64(_)
        | ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _) => None,
        // A `Bool` value decides by its shape, as the kernel decides it
        // with no facts.
        ConditionTerm::BoolApplication(_)
        | ConditionTerm::BoolIf { .. }
        | ConditionTerm::BoolEqual(..)
        | ConditionTerm::BoolLoad(..) => {
            crate::kernel::SelectedFacts::from_propositions(&[]).decide_selected_condition(condition)
        }
    }
}

pub(in crate::surface) fn evaluate_bitvector_constant(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::MachineIntegerCast { .. } => None,
        // Rule C1: a decided `Bool` casts to 1 or 0.
        Bitvector32Term::BoolCast { value, .. } => {
            Some(u32::from(normalize_condition_without_assumptions(value)?))
        }

        Bitvector32Term::Constant(value) | Bitvector32Term::UInt32Constant(value) => Some(*value),
        Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::UInt32From64(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | crate::kernel::binary_wide_term!(..)
        | crate::kernel::unary_wide_term!(..)
        | Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
        | Bitvector32Term::PointerAddress(_, _)
        | Bitvector32Term::MemoryLoad(_, _, _) => None,
        binary_term!(Int32, Add, left, right) => Some(
            evaluate_bitvector_constant(left)?.wrapping_add(evaluate_bitvector_constant(right)?),
        ),
        binary_term!(Int32, Subtract, left, right) => Some(
            evaluate_bitvector_constant(left)?.wrapping_sub(evaluate_bitvector_constant(right)?),
        ),
        binary_term!(Int32, Multiply, left, right) => Some(
            evaluate_bitvector_constant(left)?.wrapping_mul(evaluate_bitvector_constant(right)?),
        ),
        binary_term!(Int32, Divide, left, right) => {
            let left = evaluate_bitvector_constant(left)? as i32;
            let right = evaluate_bitvector_constant(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left / right) as u32)
            }
        }
        binary_term!(UInt32, Divide, left, right) => {
            let left = evaluate_bitvector_constant(left)?;
            let right = evaluate_bitvector_constant(right)?;
            left.checked_div(right)
        }
        binary_term!(Int32, Remainder, left, right) => {
            let left = evaluate_bitvector_constant(left)? as i32;
            let right = evaluate_bitvector_constant(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left % right) as u32)
            }
        }
        binary_term!(UInt32, Remainder, left, right) => {
            let left = evaluate_bitvector_constant(left)?;
            let right = evaluate_bitvector_constant(right)?;
            left.checked_rem(right)
        }
        binary_term!(Int32, ShiftLeft, left, right) => {
            let left = evaluate_bitvector_constant(left)? as i32;
            let right = bitvector32_shift_count(evaluate_bitvector_constant(right)?)?;
            if left < 0 {
                None
            } else {
                let shifted = (left as i64) << right;
                (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
            }
        }
        binary_term!(Int32, ShiftRight, left, right) => {
            let left = evaluate_bitvector_constant(left)? as i32;
            let right = bitvector32_shift_count(evaluate_bitvector_constant(right)?)?;
            Some((left >> right) as u32)
        }
        binary_term!(UInt32, ShiftRight, left, right) => {
            let left = evaluate_bitvector_constant(left)?;
            let right = bitvector32_shift_count(evaluate_bitvector_constant(right)?)?;
            Some(left >> right)
        }
        binary_term!(Int32, BitwiseAnd, left, right) => {
            Some(evaluate_bitvector_constant(left)? & evaluate_bitvector_constant(right)?)
        }
        binary_term!(Int32, BitwiseOr, left, right) => {
            Some(evaluate_bitvector_constant(left)? | evaluate_bitvector_constant(right)?)
        }
        binary_term!(Int32, BitwiseXor, left, right) => {
            Some(evaluate_bitvector_constant(left)? ^ evaluate_bitvector_constant(right)?)
        }
        unary_term!(Int32, BitwiseNot, value) => Some(!evaluate_bitvector_constant(value)?),
        // A 32-bit sign-free operator is built at `int32` only.
        Bitvector32Term::Binary { .. } => None,
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match normalize_condition_without_assumptions(condition)? {
            true => evaluate_bitvector_constant(then_term),
            false => evaluate_bitvector_constant(else_term),
        },
        Bitvector32Term::IntegerToMachine { .. } => None,
    }
}

pub(in crate::surface) fn normalize_bitvector(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::UInt32Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::IntegerToMachine { .. } => term.clone(),
        Bitvector32Term::BoolCast { value, .. } => {
            match normalize_condition_without_assumptions(value) {
                Some(value) => Bitvector32Term::Constant(u32::from(value)),
                None => term.clone(),
            }
        }
        binary_term!(Int32, Add, left, right) => {
            bitvector32_add(normalize_bitvector(left), normalize_bitvector(right))
        }
        binary_term!(Int32, Subtract, left, right) => {
            bitvector32_subtract(normalize_bitvector(left), normalize_bitvector(right))
        }
        binary_term!(Int32, Multiply, left, right) => {
            bitvector32_multiply(normalize_bitvector(left), normalize_bitvector(right))
        }
        binary_term!(Int32, Divide, left, right) => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            bitvector32_divide(left.clone(), right.clone())
                .unwrap_or_else(|_| binary_node!(Int32, Divide, Box::new(left), Box::new(right)))
        }
        binary_term!(Int32, Remainder, left, right) => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            bitvector32_remainder(left.clone(), right.clone())
                .unwrap_or_else(|_| binary_node!(Int32, Remainder, Box::new(left), Box::new(right)))
        }
        binary_term!(Int32, ShiftLeft, left, right) => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            bitvector32_shift_left(left.clone(), right.clone())
                .unwrap_or_else(|_| binary_node!(Int32, ShiftLeft, Box::new(left), Box::new(right)))
        }
        binary_term!(Int32, ShiftRight, left, right) => {
            let left = normalize_bitvector(left);
            let right = normalize_bitvector(right);
            bitvector32_shift_right(left.clone(), right.clone()).unwrap_or_else(|_| {
                binary_node!(Int32, ShiftRight, Box::new(left), Box::new(right))
            })
        }
        binary_term!(Int32, BitwiseAnd, left, right) => {
            bitvector32_and(normalize_bitvector(left), normalize_bitvector(right))
        }
        binary_term!(Int32, BitwiseOr, left, right) => {
            bitvector32_or(normalize_bitvector(left), normalize_bitvector(right))
        }
        binary_term!(Int32, BitwiseXor, left, right) => {
            bitvector32_xor(normalize_bitvector(left), normalize_bitvector(right))
        }
        unary_term!(Int32, BitwiseNot, value) => bitvector32_not(normalize_bitvector(value)),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match normalize_condition_without_assumptions(condition) {
            Some(true) => normalize_bitvector(then_term),
            Some(false) => normalize_bitvector(else_term),
            None => Bitvector32Term::if_then_else(
                condition.as_ref().clone(),
                normalize_bitvector(then_term),
                normalize_bitvector(else_term),
            ),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::range_fold(
            normalize_bitvector(start),
            normalize_bitvector(end),
            normalize_bitvector(initial),
            *accumulator,
            *item,
            normalize_bitvector(body),
        ),
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments.iter().map(normalize_bitvector).collect(),
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
            Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone(), *kind)
        }
        Bitvector32Term::PointerAddress(_, _) => term.clone(),
        term => match (term.as_binary(), term.as_unary()) {
            (Some((op, left, right)), _) => {
                op.build(normalize_bitvector(left), normalize_bitvector(right))
            }
            (_, Some((op, value))) => op.build(normalize_bitvector(value)),
            _ => unreachable!("every other variant has its own arm"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType, SharedIntegerRangeEndpoint,
        SharedMachineIntegerTerm,
    };

    /// The equality-rewrite search visits premise orders depth first, and a
    /// goal it cannot close makes it visit all of them. Under an exhausted
    /// deadline it stops at its first node.
    #[test]
    #[ignore = "nightly: 1.8s in the parallel gate"]
    fn equality_rewrite_search_observes_the_deadline() {
        let variable = |index: u64| Bitvector32Term::Variable(Variable(93_400 + index));
        let count = 6;
        let sum = (1..count).fold(variable(0), |sum, index| {
            Bitvector32Term::add(sum, variable(index))
        });
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(sum),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );
        let premises = (0..count)
            .map(|index| {
                let kernel = Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(variable(index)),
                        right: Box::new(variable(100 + index)),
                    },
                    true,
                );
                let surface = ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral(index.to_string()),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::IntegerLiteral((100 + index).to_string()),
                };
                (kernel, surface)
            })
            .collect::<Vec<_>>();
        let available = premises
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let nodes = std::cell::Cell::new(0_usize);
        let closer = |_: &Proposition| {
            nodes.set(nodes.get() + 1);
            None
        };
        let unbounded =
            plan_explicit_equality_rewrites_from(&goal, &premises, &available, &|_| false, &closer);
        assert!(unbounded.is_none());
        assert!(
            nodes.get() > 1_000,
            "an unclosable goal visits every premise order: {} nodes",
            nodes.get()
        );
        nodes.set(0);
        let expired = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            plan_explicit_equality_rewrites_from(&goal, &premises, &available, &|_| false, &closer)
        });
        assert!(expired.is_none());
        assert_eq!(
            nodes.get(),
            0,
            "an exhausted deadline stops the search at once"
        );
    }

    #[test]
    fn registered_pointer_rewrite_uses_observed_snapshot() {
        // Projected identity snapshots have no target-cell content. Rewriting
        // the address must use the observed snapshot, including its latest
        // overwrite, rather than inventing a disconnected target load.
        for (case, stored) in [(0, 17), (1, 29)] {
            let source = Pointer::symbolic(Variable(910_000 + case));
            let target = Pointer {
                block: PointerBlock::Heap(920_000 + case),
                offset: PointerOffsetTerm::Constant(4),
            };
            let identity = crate::kernel::intern_c_memory(
                CMemory::new().with_block(format!("rewrite-origin-{case}"), 16),
            );
            let observed = crate::kernel::intern_c_memory(
                identity
                    .memory()
                    .clone()
                    .store(target.clone(), CValue::Int32(Bitvector32Term::Constant(17)))
                    .store(
                        target.clone(),
                        CValue::Int32(Bitvector32Term::Constant(stored)),
                    ),
            );
            let load = crate::kernel::load_variable_for_cell_with_origin(
                &identity,
                &source,
                crate::kernel::LoadKind::Int32,
                4,
                &observed,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(Bitvector32Term::Variable(load)),
                    right: Box::new(Bitvector32Term::Constant(17)),
                },
                true,
            );
            let equality =
                Proposition::ConditionIs(ConditionTerm::pointer_equal(source, target), true);
            let rewritten = rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality),
            )
            .expect("rewrite the registered load at its observed snapshot");
            // The rewritten goal reads the target at the observed snapshot,
            // named as a read: the read-over-write authority relates it to
            // the latest overwrite stored there.
            let Proposition::ConditionIs(ConditionTerm::Compare { left, right, .. }, true) =
                &rewritten
            else {
                panic!("the rewrite keeps the comparison: {rewritten:?}");
            };
            assert_eq!(right.as_ref(), &Bitvector32Term::Constant(17));
            assert_ne!(left.as_ref(), &Bitvector32Term::Variable(load));
            assert_eq!(
                crate::kernel::read_over_write_value(left),
                Some(Bitvector32Term::Constant(stored))
            );
        }
    }

    #[test]
    fn pointer_rewrite_reaches_through_a_loaded_pointer() {
        // `w` is the pointer read from `source`. Rewriting `source` to
        // `target` rewrites the load `w` names, so a read through `w`
        // becomes a read through the pointer read from `target`.
        let source = Pointer::symbolic(Variable(930_000));
        let target = Pointer {
            block: PointerBlock::Heap(930_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = crate::kernel::intern_c_memory(
            CMemory::new().with_block(PointerBlock::Heap(930_001), 16),
        );
        let loaded = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &source,
            crate::kernel::LoadKind::Int32,
            8,
            &memory,
        );
        let (target_loaded, _) =
            crate::kernel::load_variable_for_term(&Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(target.clone()),
                crate::kernel::LoadKind::Int32,
            ))
            .expect("the target read has a name");
        let read_through = |variable| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: PointerBlock::Symbolic(variable),
                    offset: PointerOffsetTerm::Constant(8),
                }),
                crate::kernel::LoadKind::Int32,
            )
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(read_through(loaded)),
                right: Box::new(Bitvector32Term::Constant(5)),
            },
            true,
        );
        let equality = Proposition::ConditionIs(ConditionTerm::pointer_equal(source, target), true);
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("rewrite through the loaded pointer");
        assert_eq!(
            rewritten,
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(read_through(target_loaded)),
                    right: Box::new(Bitvector32Term::Constant(5))
                },
                true,
            )
        );
    }

    #[test]
    fn pointer_rewrite_changes_every_matching_field_load_at_one_snapshot() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let source = Pointer {
            block: PointerBlock::Symbolic(Variable(91)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
        };
        let field_load = |base: &Pointer, displacement| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::add(
                        base.offset.clone(),
                        PointerOffsetTerm::Constant(displacement),
                    ),
                }),
                crate::kernel::LoadKind::Int32,
            )
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(source.clone(), target.clone()),
            true,
        );
        let goal = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(field_load(&source, 4)),
                    right: Box::new(field_load(&target, 4)),
                },
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(field_load(&source, 8)),
                    right: Box::new(field_load(&target, 12)),
                },
                true,
            )),
        );
        assert!(
            rewrite_proposition_by_exact_equality(&goal, &equality, &[])
                .expect_err("the equality must be available")
                .contains("exact available fact")
        );
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("one cited equality rewrites both field addresses");
        let expected = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(field_load(&target, 4)),
                    right: Box::new(field_load(&target, 4)),
                },
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(field_load(&target, 8)),
                    right: Box::new(field_load(&target, 12)),
                },
                true,
            )),
        );
        assert_eq!(rewritten, expected);
    }

    #[test]
    fn rewrite_uses_pointer_offset_equalities_inside_pointer_goals() {
        let left = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(41))),
            byte_width: 4,
        };
        let right = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(42))),
            byte_width: 4,
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        );
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let null = Pointer {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer(left), null.clone()),
            true,
        );

        assert_eq!(
            rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality),
            )
            .unwrap(),
            Proposition::ConditionIs(ConditionTerm::pointer_equal(pointer(right), null), true,),
        );
    }

    #[test]
    fn rewrite_substitutes_index_and_base_equalities_inside_load_addresses() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let data = Bitvector32Term::Variable(Variable(51));
        let alias = Bitvector32Term::Variable(Variable(52));
        let index = Bitvector32Term::Variable(Variable(53));
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let load = |offset| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(pointer(offset)),
                crate::kernel::LoadKind::Int32,
            )
        };
        let data_offset = PointerOffsetTerm::scale_int32(data.clone(), 4);
        let alias_offset = PointerOffsetTerm::scale_int32(alias.clone(), 4);
        let indexed_offset = PointerOffsetTerm::add(
            data_offset.clone(),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load(indexed_offset)),
                right: Box::new(load(alias_offset.clone())),
            },
            true,
        );
        let index_is_zero = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(index),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );
        let data_is_alias = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(data_offset), Box::new(alias_offset)),
            true,
        );
        let available = [index_is_zero.clone(), data_is_alias.clone()];

        let indexed =
            rewrite_proposition_by_exact_equality(&goal, &index_is_zero, &available).unwrap();
        let aliased =
            rewrite_proposition_by_exact_equality(&indexed, &data_is_alias, &available).unwrap();
        assert_eq!(normalize_proposition(&aliased), NormalizedProposition::True);
    }

    #[test]
    fn rewrite_substitutes_length_and_base_equalities_inside_memory_resources() {
        let source = Bitvector32Term::Variable(Variable(61));
        let target = Bitvector32Term::Variable(Variable(62));
        let source_len = Bitvector32Term::Variable(Variable(63));
        let target_len = Bitvector32Term::Variable(Variable(64));
        let fixed = CResource::Memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(65)), 4),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        ));
        let range = |base: Bitvector32Term, end: Bitvector32Term| {
            CResource::Memory(CMemoryRange::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(base, 4),
                },
                Bitvector32Term::Constant(0),
                end,
            ))
        };
        let goal = Proposition::CResourceSeparate {
            left: Box::new(fixed.clone()),
            right: Box::new(range(source.clone(), source_len.clone())),
        };
        let length_equality = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(source_len),
                right: Box::new(target_len.clone()),
            },
            true,
        );
        let base_equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(PointerOffsetTerm::scale_int32(source.clone(), 4)),
                Box::new(PointerOffsetTerm::scale_int32(target.clone(), 4)),
            ),
            true,
        );
        let available = [length_equality.clone(), base_equality.clone()];

        let resized =
            rewrite_proposition_by_exact_equality(&goal, &length_equality, &available).unwrap();
        let replaced =
            rewrite_proposition_by_exact_equality(&resized, &base_equality, &available).unwrap();
        assert_eq!(
            replaced,
            Proposition::CResourceSeparate {
                left: Box::new(fixed),
                right: Box::new(match range(source, target_len) {
                    CResource::Memory(range) => CResource::Memory(range.with_base(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::scale_int32(target, 4),
                    })),
                    _ => unreachable!(),
                }),
            }
        );
    }

    #[test]
    fn integer_solve_planner_emits_explicit_bound_certificate() {
        let x = IntegerTerm::Variable(Variable(71));
        let y = IntegerTerm::Variable(Variable(72));
        let lower = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(x.clone().into(), y.clone().into()),
            true,
        );
        let upper = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(y.clone().into(), x.clone().into()),
            true,
        );
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(x.into(), y.into()), true);
        let certificate = plan_arithmetic(
            ArithmeticEngine::IntegerAffine,
            &goal,
            &[lower.clone(), upper.clone()],
        )
        .and_then(ArithmeticPlan::integer_affine)
        .expect("opposite integer bounds should produce a certificate");
        certificate
            .check(&goal, &[lower, upper])
            .expect("the planned certificate should pass the kernel checker");
    }
    #[test]
    fn integer_observation_rewrite_requires_an_available_machine_equality() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("rewrite-cell", 4));
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let load =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Int32);
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, load.clone())
            .expect("a symbolic int32 load is a mathematical observation");
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), observed.into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );

        let error = rewrite_proposition_by_exact_equality(&goal, &equality, &[])
            .expect_err("an equality absent from the checked facts must be rejected");
        assert!(error.contains("exact available fact"), "{error}");
    }

    #[test]
    fn integer_range_fold_rewrite_changes_only_int32_endpoints() {
        let from = Bitvector32Term::Variable(Variable(71));
        let to = Bitvector32Term::Variable(Variable(72));
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("fold", 4));
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "fold".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                crate::kernel::LoadKind::Int32,
            ),
        ));
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
                end: SharedIntegerRangeEndpoint::intern(from.clone()),
            },
            IntegerTerm::constant_i64(0),
            Variable(73),
            Variable(74),
            body.clone(),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.clone().into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(from),
                right: Box::new(to.clone()),
            },
            true,
        );
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("a checked endpoint equality should rewrite the Int32 fold bound");
        let expected = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
                end: SharedIntegerRangeEndpoint::intern(to),
            },
            IntegerTerm::constant_i64(0),
            Variable(73),
            Variable(74),
            body,
        );
        assert_eq!(
            rewritten,
            Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(expected.into(), IntegerTerm::constant_i64(0).into()),
                true,
            )
        );
    }

    #[test]
    fn integer_range_fold_rewrite_rejects_missing_or_integer_bound_equalities() {
        let from = Bitvector32Term::Variable(Variable(81));
        let to = Bitvector32Term::Variable(Variable(82));
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::var(Variable(81)).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(83),
            Variable(84),
            IntegerTerm::add(
                IntegerTerm::var(Variable(83)),
                IntegerTerm::var(Variable(84)),
            ),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(from),
                right: Box::new(to),
            },
            true,
        );
        let missing = rewrite_proposition_by_exact_equality(&goal, &equality, &[])
            .expect_err("an absent endpoint equality must be rejected");
        assert!(missing.contains("exact available fact"), "{missing}");
        let unchanged = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect_err("machine equality must not rewrite an Integer range bound");
        assert!(unchanged.contains("does not occur"), "{unchanged}");
    }

    #[test]
    fn integer_observation_rewrite_does_not_cross_memory_snapshots() {
        let pointer = Pointer {
            block: PointerBlock::Concrete("rewrite-cell".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first_memory = crate::kernel::intern_c_memory(
            CMemory::new()
                .with_block("rewrite-cell", 4)
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0))),
        );
        let second_memory = crate::kernel::intern_c_memory(
            CMemory::new()
                .with_block("rewrite-cell", 4)
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
        );
        assert_ne!(first_memory, second_memory);
        let first_load = Bitvector32Term::MemoryLoad(
            first_memory,
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        );
        let second_load = Bitvector32Term::MemoryLoad(
            second_memory,
            Box::new(pointer),
            crate::kernel::LoadKind::Int32,
        );
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, second_load)
            .expect("a symbolic int32 load is a mathematical observation");
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), observed.into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(first_load),
                right: Box::new(Bitvector32Term::Constant(0)),
            },
            true,
        );

        let error = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect_err("a checked equality from another memory snapshot must not rewrite this load");
        assert!(
            error.contains("does not occur in the current goal"),
            "{error}"
        );
    }
}

#[cfg(test)]
mod partial_arithmetic_tests {
    use super::*;

    #[test]
    fn unsigned_constant_division_and_remainder_leave_zero_undefined() {
        for operator in [
            crate::kernel::MachineBinaryOp::Divide,
            crate::kernel::MachineBinaryOp::Remainder,
        ] {
            for (divisor, expected) in [
                (0, None),
                (
                    2,
                    Some(if operator == crate::kernel::MachineBinaryOp::Divide {
                        2
                    } else {
                        1
                    }),
                ),
            ] {
                let term = Bitvector32Term::machine_binary(
                    crate::kernel::MachineIntegerType::UInt32,
                    operator,
                    Bitvector32Term::UInt32Constant(5),
                    Bitvector32Term::UInt32Constant(divisor),
                );
                assert_eq!(evaluate_bitvector_constant(&term), expected);
            }
        }
    }
}
