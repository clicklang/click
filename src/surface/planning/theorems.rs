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

fn parameter_name(expression: &ContractExpression) -> Option<&str> {
    match expression {
        ContractExpression::Binding(name) | ContractExpression::AlgebraicVariable { name, .. } => {
            Some(name)
        }
        ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) => name.named(),
        _ => None,
    }
}

fn expression_head(expression: &ContractExpression) -> ExpressionHead {
    use ContractExpression as E;
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

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum ConclusionHead {
    Comparison(u8, Option<ExpressionHead>, Option<ExpressionHead>),
    Predicate(String),
    Defined(Option<ExpressionHead>),
    Value(Option<ExpressionHead>),
    Logical(u8),
}

fn conclusion_head(
    proposition: &ClickProposition,
    parameters: &BTreeSet<&str>,
) -> Option<ConclusionHead> {
    let head = |expression: &ContractExpression| {
        if parameter_name(expression).is_some_and(|name| parameters.contains(name)) {
            None
        } else {
            Some(expression_head(expression))
        }
    };
    Some(match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ConclusionHead::Comparison(*operator as u8, head(left), head(right)),
        ClickProposition::PredicateCall { name, .. } => ConclusionHead::Predicate(name.clone()),
        ClickProposition::Defined { expression } => ConclusionHead::Defined(head(expression)),
        ClickProposition::Value(expression) => ConclusionHead::Value(head(expression)),
        ClickProposition::And(..) => ConclusionHead::Logical(0),
        ClickProposition::Or(..) => ConclusionHead::Logical(1),
        ClickProposition::Not(..) => ConclusionHead::Logical(2),
        ClickProposition::Implies(..) => ConclusionHead::Logical(3),
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
        goal: &ClickProposition,
        end: usize,
    ) -> impl Iterator<Item = &'a TheoremCandidate> {
        let mut keys = Vec::new();
        if let Some(key) = conclusion_head(goal, &BTreeSet::new()) {
            match &key {
                ConclusionHead::Comparison(operator, left, right) => {
                    keys.push(ConclusionHead::Comparison(*operator, None, right.clone()));
                    keys.push(ConclusionHead::Comparison(*operator, left.clone(), None));
                    keys.push(ConclusionHead::Comparison(*operator, None, None));
                }
                ConclusionHead::Defined(_) => keys.push(ConclusionHead::Defined(None)),
                ConclusionHead::Value(_) => keys.push(ConclusionHead::Value(None)),
                _ => {}
            }
            keys.insert(0, key);
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

/// Binder-free structural matching. Repeated parameters must have the same
/// source argument; arbitrary equivalence and argument synthesis are deferred.
pub(in crate::surface) fn match_theorem_conclusion(
    theorem: &TheoremDefinition,
    ensure: usize,
    goal: &ClickProposition,
) -> Option<TheoremApplication> {
    use ClickProposition as P;
    use ContractExpression as E;
    enum Pair<'a> {
        Expression(&'a E, &'a E),
        Proposition(&'a P, &'a P),
    }
    let Ensure::Proposition(conclusion) = theorem.ensures().get(ensure)?.ensure() else {
        return None;
    };
    let parameters = theorem
        .parameters()
        .iter()
        .map(FunctionParameter::name)
        .collect::<BTreeSet<_>>();
    let mut arguments = BTreeMap::<&str, ContractExpression>::new();
    let mut pending = vec![Pair::Proposition(conclusion, goal)];
    while let Some(pair) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
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
                ) if po == ao => {
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
                _ => return None,
            },
            Pair::Expression(pattern, actual) => {
                if let Some(name) = parameter_name(pattern).filter(|name| parameters.contains(name))
                {
                    if let Some(prior) = arguments.get(name) {
                        if prior != actual {
                            return None;
                        }
                    } else {
                        arguments.insert(name, actual.clone());
                    }
                    continue;
                }
                match (pattern, actual) {
                    (binary_contract_expression!(pl, pr), binary_contract_expression!(al, ar))
                        if std::mem::discriminant(pattern) == std::mem::discriminant(actual) =>
                    {
                        pending.extend([Pair::Expression(pl, al), Pair::Expression(pr, ar)]);
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
                        pending.extend(pa.iter().zip(aa).map(|(p, a)| Pair::Expression(p, a)));
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
                        pending.extend(pa.iter().zip(aa).map(|(p, a)| Pair::Expression(p, a)));
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
                    (E::Proposition(p), E::Proposition(a)) => pending.push(Pair::Proposition(p, a)),
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
                    _ => return None,
                }
            }
        }
    }
    Some(TheoremApplication {
        name: theorem.name().into(),
        arguments: theorem
            .parameters()
            .iter()
            .map(|parameter| arguments.get(parameter.name()).cloned())
            .collect::<Option<_>>()?,
    })
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../scaling_tests/surface/planning/theorems.rs");
}
