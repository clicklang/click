//! Indexed, one-application theorem discovery for premise-restricted solve.
//! Matching proposes source arguments only; ordinary `apply using` constructs
//! the checked successor and enforces types, guards, and every requirement.
use crate::surface::*;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ExpressionHead {
    Call(String),
    Constructor(String, String),
    Node(&'static str),
}

fn parameter_name(expression: &SyntaxTerm) -> Option<&str> {
    match expression {
        SyntaxTerm::AlgebraicVariable { name, .. } => name.written(),
        SyntaxTerm::Binding(name) => Some(name),
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)) => name.named(),
        _ => None,
    }
}

fn expression_head(expression: &SyntaxTerm) -> ExpressionHead {
    use SyntaxTerm as E;
    ExpressionHead::Node(match expression {
        E::Call { name, .. } => return ExpressionHead::Call(name.clone()),
        E::AlgebraicConstructor {
            algebraic_type,
            variant,
            ..
        } => {
            return ExpressionHead::Constructor(algebraic_type.name.clone(), variant.clone());
        }
        E::Add(..) => "add",
        E::Subtract(..) => "subtract",
        E::Multiply(..) => "multiply",
        E::Divide(..) => "divide",
        E::Remainder(..) => "remainder",
        E::ShiftLeft(..) => "shl",
        E::ShiftRight(..) => "shr",
        E::RustShiftLeft(..) => "rust_shl",
        E::RustShiftRight(..) => "rust_shr",
        E::BitwiseAnd(..) => "and",
        E::BitwiseOr(..) => "or",
        E::BitwiseXor(..) => "xor",
        E::Index(..) => "index",
        E::Negate(..) => "negate",
        E::BitwiseNot(..) => "not",
        E::Old(..) => "old",
        E::At { .. } => "at",
        E::Field { .. } => "field",
        E::CUnary { .. } => "c_unary",
        E::If { .. } => "if",
        E::IntegerLiteral(..) => "literal",
        E::Proposition(..) => "proposition",
        _ => "other",
    })
}

/// Operand reversal preserves float comparisons too, including NaNs. Do not
/// turn negated orders into complementary relations here.
fn comparison_view<'a>(
    left: &'a SyntaxTerm,
    operator: ComparisonOperator,
    right: &'a SyntaxTerm,
) -> (ComparisonOperator, &'a SyntaxTerm, &'a SyntaxTerm) {
    match operator {
        ComparisonOperator::GreaterThan => (ComparisonOperator::LessThan, right, left),
        ComparisonOperator::GreaterEqual => (ComparisonOperator::LessEqual, right, left),
        _ => (operator, left, right),
    }
}

fn symmetric_comparison(operator: ComparisonOperator) -> bool {
    matches!(
        operator,
        ComparisonOperator::Equal | ComparisonOperator::NotEqual
    )
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ConclusionHead {
    Comparison(u8, Option<ExpressionHead>, Option<ExpressionHead>),
    Predicate(String),
    Defined(Option<ExpressionHead>),
    Value(Option<ExpressionHead>),
    Logical(u8),
}

fn conclusion_head(
    proposition: &SyntaxProposition,
    parameters: &BTreeSet<&str>,
) -> Option<ConclusionHead> {
    let head = |expression: &SyntaxTerm| {
        if parameter_name(expression).is_some_and(|name| parameters.contains(name)) {
            None
        } else {
            Some(expression_head(expression))
        }
    };
    Some(match proposition {
        SyntaxProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let (operator, left, right) = comparison_view(left, *operator, right);
            ConclusionHead::Comparison(operator as u8, head(left), head(right))
        }
        SyntaxProposition::PredicateCall { name, .. } => ConclusionHead::Predicate(name.clone()),
        SyntaxProposition::Defined { expression } => ConclusionHead::Defined(head(expression)),
        SyntaxProposition::Value(expression) => ConclusionHead::Value(head(expression)),
        SyntaxProposition::And(..) => ConclusionHead::Logical(0),
        SyntaxProposition::Or(..) => ConclusionHead::Logical(1),
        SyntaxProposition::Not(..) => ConclusionHead::Logical(2),
        SyntaxProposition::Implies(..) => ConclusionHead::Logical(3),
        _ => return None,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct TheoremCandidate {
    pub name: String,
    pub ensure: usize,
}

/// Persistent indexes keep insertion and sharing proportional to one theorem.
/// The inner order key lets a library prefix stop before later declarations.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(in crate::surface) struct TheoremConclusionIndex {
    buckets: PersistentMap<ConclusionHead, PersistentMap<(usize, usize), TheoremCandidate>>,
}

impl TheoremConclusionIndex {
    pub(in crate::surface) fn insert(&mut self, theorem: &TheoremDefinition, ordinal: usize) {
        if theorem.executes.is_some()
            || theorem
                .requires()
                .iter()
                .any(|requirement| requirement.theorem_proposition().is_none())
        {
            return;
        }
        let parameters = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .collect();
        for (ensure, clause) in theorem.ensures().iter().enumerate() {
            let Ensure::Proposition(conclusion) = clause.ensure() else {
                continue;
            };
            let Some(key) = conclusion_head(conclusion, &parameters) else {
                continue;
            };
            crate::instrumentation::record_deterministic_work(1);
            let mut bucket = self.buckets.get(&key).cloned().unwrap_or_default();
            bucket.insert(
                (ordinal, ensure),
                TheoremCandidate {
                    name: theorem.name().into(),
                    ensure,
                },
            );
            self.buckets.insert(key, bucket);
        }
    }

    pub(in crate::surface) fn candidates<'a>(
        &'a self,
        goal: &SyntaxProposition,
        end: usize,
    ) -> impl Iterator<Item = &'a TheoremCandidate> {
        let mut keys = Vec::new();
        let mut add = |key| {
            if !keys.contains(&key) {
                keys.push(key);
            }
        };
        if let Some(key) = conclusion_head(goal, &BTreeSet::new()) {
            let mut heads = vec![key];
            if let ConclusionHead::Comparison(operator, left, right) = &heads[0]
                && (*operator == ComparisonOperator::Equal as u8
                    || *operator == ComparisonOperator::NotEqual as u8)
            {
                heads.push(ConclusionHead::Comparison(
                    *operator,
                    right.clone(),
                    left.clone(),
                ));
            }
            for key in heads {
                add(key.clone());
                match key {
                    ConclusionHead::Comparison(operator, left, right) => {
                        add(ConclusionHead::Comparison(operator, None, right));
                        add(ConclusionHead::Comparison(operator, left, None));
                        add(ConclusionHead::Comparison(operator, None, None));
                    }
                    ConclusionHead::Defined(_) => add(ConclusionHead::Defined(None)),
                    ConclusionHead::Value(_) => add(ConclusionHead::Value(None)),
                    _ => {}
                }
            }
        }
        let buckets = keys
            .into_iter()
            .filter_map(|key| {
                crate::instrumentation::record_deterministic_work(1);
                self.buckets.get(&key)
            })
            .collect::<Vec<_>>();
        buckets.into_iter().flat_map(move |bucket| {
            bucket
                .iter()
                .take_while(move |((ordinal, _), _)| *ordinal < end)
                .map(|(_, candidate)| {
                    crate::instrumentation::record_deterministic_work(1);
                    candidate
                })
        })
    }
}

/// Outcomes from the existing structural walk; no additional candidate search.
pub(in crate::surface) enum TheoremConclusionMatch<'a> {
    Application(TheoremApplication),
    UndeterminedArgument(&'a str),
    Exhausted,
}

#[cfg(test)]
pub(in crate::surface) fn match_theorem_conclusion<'a>(
    theorem: &'a TheoremDefinition,
    ensure: usize,
    goal: &'a SyntaxProposition,
) -> impl Iterator<Item = TheoremApplication> + 'a {
    theorem_conclusion_matches(theorem, ensure, goal).filter_map(|outcome| match outcome {
        TheoremConclusionMatch::Application(application) => Some(application),
        _ => None,
    })
}

/// Lazy structural matches, including both orientations of symmetric
/// comparisons. Keep alternatives so later occurrences and listed theorem
/// prerequisites can disambiguate the argument assignment.
pub(in crate::surface) fn theorem_conclusion_matches<'a>(
    theorem: &'a TheoremDefinition,
    ensure: usize,
    goal: &'a SyntaxProposition,
) -> impl Iterator<Item = TheoremConclusionMatch<'a>> + 'a {
    use SyntaxProposition as P;
    use SyntaxTerm as E;
    #[derive(Clone, Copy)]
    enum Pair<'a> {
        Expression(&'a E, &'a E),
        Proposition(&'a P, &'a P),
    }
    let conclusion = theorem
        .ensures()
        .get(ensure)
        .and_then(|clause| match clause.ensure() {
            Ensure::Proposition(conclusion) => Some(conclusion),
            _ => None,
        });
    let parameters = theorem
        .parameters()
        .iter()
        .map(FunctionParameter::name)
        .collect::<BTreeSet<_>>();
    let mut alternatives = conclusion
        .into_iter()
        .map(|conclusion| {
            (
                BTreeMap::<&str, &SyntaxTerm>::new(),
                vec![Pair::Proposition(conclusion, goal)],
            )
        })
        .collect::<Vec<_>>();
    std::iter::from_fn(move || {
        'alternative: while let Some((mut arguments, mut pending)) = alternatives.pop() {
            while let Some(pair) = pending.pop() {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    alternatives.clear();
                    return Some(TheoremConclusionMatch::Exhausted);
                }
                match pair {
                    Pair::Proposition(pattern, actual) => match (pattern, actual) {
                        (
                            P::Comparison {
                                left: pl,
                                operator: po,
                                right: pr,
                            },
                            P::Comparison {
                                left: al,
                                operator: ao,
                                right: ar,
                            },
                        ) => {
                            let (po, pl, pr) = comparison_view(pl, *po, pr);
                            let (ao, al, ar) = comparison_view(al, *ao, ar);
                            if po != ao {
                                continue 'alternative;
                            }
                            if symmetric_comparison(po) && pl != pr && al != ar {
                                if crate::instrumentation::deadline_exceeded_with_work(
                                    arguments.len() + pending.len() + 1,
                                ) {
                                    alternatives.clear();
                                    return Some(TheoremConclusionMatch::Exhausted);
                                }
                                let mut reversed = pending.clone();
                                reversed
                                    .extend([Pair::Expression(pl, ar), Pair::Expression(pr, al)]);
                                alternatives.push((arguments.clone(), reversed));
                            }
                            pending.extend([Pair::Expression(pl, al), Pair::Expression(pr, ar)]);
                        }
                        (
                            P::PredicateCall {
                                name: pn,
                                arguments: pa,
                            },
                            P::PredicateCall {
                                name: an,
                                arguments: aa,
                            },
                        ) if pn == an && pa.len() == aa.len() => {
                            pending.extend(pa.iter().zip(aa).map(|(p, a)| Pair::Expression(p, a)));
                        }
                        (P::Defined { expression: p }, P::Defined { expression: a })
                        | (P::Value(p), P::Value(a)) => pending.push(Pair::Expression(p, a)),
                        (P::And(pl, pr), P::And(al, ar))
                        | (P::Or(pl, pr), P::Or(al, ar))
                        | (P::Implies(pl, pr), P::Implies(al, ar)) => {
                            pending.extend([Pair::Proposition(pl, al), Pair::Proposition(pr, ar)]);
                        }
                        (P::Not(p), P::Not(a)) => pending.push(Pair::Proposition(p, a)),
                        _ if pattern == actual => {}
                        _ => continue 'alternative,
                    },
                    Pair::Expression(pattern, actual) => {
                        if let Some(name) =
                            parameter_name(pattern).filter(|name| parameters.contains(name))
                        {
                            if let Some(prior) = arguments.get(name) {
                                if *prior != actual {
                                    continue 'alternative;
                                }
                            } else {
                                arguments.insert(name, actual);
                            }
                            continue;
                        }
                        match (pattern, actual) {
                            (
                                binary_contract_expression!(pl, pr),
                                binary_contract_expression!(al, ar),
                            ) if std::mem::discriminant(pattern)
                                == std::mem::discriminant(actual) =>
                            {
                                pending
                                    .extend([Pair::Expression(pl, al), Pair::Expression(pr, ar)]);
                            }
                            (E::Negate(p), E::Negate(a))
                            | (E::BitwiseNot(p), E::BitwiseNot(a))
                            | (E::Old(p), E::Old(a)) => pending.push(Pair::Expression(p, a)),
                            (
                                E::At {
                                    selector: ps,
                                    expression: p,
                                },
                                E::At {
                                    selector: as_,
                                    expression: a,
                                },
                            ) if ps == as_ => pending.push(Pair::Expression(p, a)),
                            (
                                E::Call {
                                    name: pn,
                                    arguments: pa,
                                },
                                E::Call {
                                    name: an,
                                    arguments: aa,
                                },
                            ) if pn == an && pa.len() == aa.len() => {
                                pending
                                    .extend(pa.iter().zip(aa).map(|(p, a)| Pair::Expression(p, a)));
                            }
                            (
                                E::AlgebraicConstructor {
                                    algebraic_type: pt,
                                    variant: pv,
                                    arguments: pa,
                                },
                                E::AlgebraicConstructor {
                                    algebraic_type: at,
                                    variant: av,
                                    arguments: aa,
                                },
                            ) if pt.name == at.name && pv == av && pa.len() == aa.len() => {
                                pending
                                    .extend(pa.iter().zip(aa).map(|(p, a)| Pair::Expression(p, a)));
                            }
                            (
                                E::CUnary {
                                    operand: p,
                                    lowered: pl,
                                },
                                E::CUnary {
                                    operand: a,
                                    lowered: al,
                                },
                            ) if pl == al => pending.push(Pair::Expression(p, a)),
                            (
                                E::Field {
                                    base: p,
                                    field: pf,
                                    offset_bytes: po,
                                    ..
                                },
                                E::Field {
                                    base: a,
                                    field: af,
                                    offset_bytes: ao,
                                    ..
                                },
                            ) if pf == af && po == ao => pending.push(Pair::Expression(p, a)),
                            (E::Proposition(p), E::Proposition(a)) => {
                                pending.push(Pair::Proposition(p, a))
                            }
                            (
                                E::If {
                                    condition: pc,
                                    then_branch: pt,
                                    else_branch: pe,
                                },
                                E::If {
                                    condition: ac,
                                    then_branch: at,
                                    else_branch: ae,
                                },
                            ) => {
                                pending.extend([
                                    Pair::Proposition(pc, ac),
                                    Pair::Expression(pt, at),
                                    Pair::Expression(pe, ae),
                                ]);
                            }
                            _ if pattern == actual => {}
                            _ => continue 'alternative,
                        }
                    }
                }
            }
            return Some(
                match theorem
                    .parameters()
                    .iter()
                    .map(|parameter| {
                        arguments
                            .get(parameter.name())
                            .map(|expression| (*expression).clone())
                            .ok_or(parameter.name())
                    })
                    .collect::<Result<Vec<_>, _>>()
                {
                    Ok(arguments) => TheoremConclusionMatch::Application(TheoremApplication {
                        name: theorem.name().into(),
                        arguments,
                    }),
                    Err(name) => TheoremConclusionMatch::UndeterminedArgument(name),
                },
            );
        }
        None
    })
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/surface/planning/theorems.rs");
}
