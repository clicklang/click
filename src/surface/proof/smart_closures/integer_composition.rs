//! Ordinary proofs of the composition fragment of Integer arithmetic plans.
//! Node results use flat linear forms over the original source operands. A
//! node never embeds another node's source tree, even when the plan is a DAG.
use super::*;
use crate::kernel::{IntegerTerm, SharedIntegerTerm};

#[derive(Clone, Default)]
struct Form {
    terms: BTreeMap<u64, BigInt>,
    constant: BigInt,
}

impl Form {
    fn scaled(&self, factor: &BigInt) -> Self {
        Self {
            terms: self
                .terms
                .iter()
                .filter_map(|(key, value)| {
                    let value = value * factor;
                    (!value.is_zero()).then_some((*key, value))
                })
                .collect(),
            constant: &self.constant * factor,
        }
    }
    fn add(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.constant += &other.constant;
        for (key, value) in &other.terms {
            *result.terms.entry(*key).or_default() += value;
        }
        result.terms.retain(|_, value| !value.is_zero());
        result
    }
}

struct Atom {
    // Retain the interned term for as long as its id keys a source operand.
    _term: SharedIntegerTerm,
    surface: ContractExpression,
}

struct Node {
    form: Form,
    equal: bool,
    claim: ClickProposition,
    semantic: IntegerAffineClaim,
}

fn literal(value: &BigInt) -> ContractExpression {
    // A fixed-width literal already carries its parsed bits. Observing it
    // keeps repeated large endpoints exact without repeatedly parsing an
    // arbitrary-precision decimal in every theorem argument.
    if value.bits() > 31
        && let Some(magnitude) = num_traits::ToPrimitive::to_u64(&value.abs())
    {
        let observed = ContractExpression::Call {
            name: "to_integer".into(),
            arguments: vec![ContractExpression::ProgramExpression(
                ProgramExpression::Value(crate::kernel::uint64(MachineTerm::uint64_constant(
                    magnitude,
                ))),
            )],
        };
        return if value.is_negative() {
            ContractExpression::Negate(Box::new(observed))
        } else {
            observed
        };
    }
    surface_signed_integer_literal(value)
}
fn zero() -> ContractExpression {
    literal(&BigInt::zero())
}
fn add(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Add(Box::new(a), Box::new(b))
}
fn multiply(a: ContractExpression, b: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(a), Box::new(b))
}
fn compare(a: ContractExpression, equal: bool, b: ContractExpression) -> ClickProposition {
    // A detached reflexivity or substitution identity has no surrounding
    // Integer operand. Keep constant arithmetic exact in that position too.
    let mut pending = vec![&a, &b];
    let mut closed = true;
    while let Some(term) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match term {
            ContractExpression::IntegerLiteral(_) => {}
            ContractExpression::Negate(value) => pending.push(value),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                pending.extend([left.as_ref(), right.as_ref()])
            }
            _ => {
                closed = false;
                break;
            }
        }
    }
    let a = if closed {
        super::super::surface_synthesis::integer_typed_expression(a)
    } else {
        a
    };
    ClickProposition::Comparison {
        left: a,
        operator: if equal {
            ComparisonOperator::Equal
        } else {
            ComparisonOperator::LessEqual
        },
        right: b,
    }
}
fn application(
    name: &str,
    arguments: Vec<ContractExpression>,
    premises: Vec<ClickProposition>,
) -> ProofStep {
    ProofStep::ApplyTheoremUsing {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}
fn have(claim: ClickProposition, steps: Vec<ProofStep>) -> ProofStep {
    super::super::wide_arithmetic::have(claim, steps)
}
fn trivial_arithmetic_step(claim: ClickProposition) -> ProofStep {
    ProofStep::ArithmeticCertificate(ArithmeticCertificate::integer(IntegerCertificate {
        nodes: vec![IntegerCertificateNode::Trivial { result: claim }],
        conclusion: 0,
    }))
}
fn arithmetic_identity(claim: ClickProposition) -> ProofStep {
    have(claim.clone(), vec![trivial_arithmetic_step(claim)])
}

fn expression(form: &Form, atoms: &BTreeMap<u64, Atom>) -> ContractExpression {
    if form.terms.is_empty() {
        // A constant-only comparison otherwise defaults to machine arithmetic.
        // Keep its type in source, including after expansion is parsed again.
        return ContractExpression::Let {
            name: "integer_constant".into(),
            click_type: Some(ClickType::Integer),
            value: Box::new(literal(&form.constant)),
            body: Box::new(ContractExpression::Binding("integer_constant".into())),
        };
    }
    let mut result = None;
    for (key, coefficient) in &form.terms {
        let term = atoms[key].surface.clone();
        let term = if coefficient.is_one() {
            term
        } else {
            multiply(literal(coefficient), term)
        };
        result = Some(match result {
            None => term,
            Some(previous) => add(previous, term),
        });
    }
    if !form.constant.is_zero() || result.is_none() {
        let constant = literal(&form.constant);
        result = Some(match result {
            None => constant,
            Some(previous) => add(previous, constant),
        });
    }
    result.expect("a linear form includes its zero")
}

fn operand(
    term: &SharedIntegerTerm,
    surface: ContractExpression,
    atoms: &mut BTreeMap<u64, Atom>,
) -> Form {
    if let Some(constant) = term.as_const() {
        return Form {
            constant: constant.clone(),
            ..Form::default()
        };
    }
    atoms.entry(term.id()).or_insert_with(|| Atom {
        _term: term.clone(),
        surface,
    });
    Form {
        terms: BTreeMap::from([(term.id(), BigInt::one())]),
        constant: BigInt::zero(),
    }
}

pub(super) fn parts(
    proposition: &Proposition,
) -> Option<(&SharedIntegerTerm, bool, &SharedIntegerTerm)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a, b), true) => {
            Some((a, false, b))
        }
        Proposition::ConditionIs(ConditionTerm::IntegerGreaterEqual(a, b), true) => {
            Some((b, false, a))
        }
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) => Some((a, true, b)),
        _ => None,
    }
}

#[derive(Clone)]
struct Reading {
    left: SharedIntegerTerm,
    right: SharedIntegerTerm,
    equal: bool,
    strict: bool,
}

fn reading(proposition: &Proposition) -> Option<Reading> {
    let mut proposition = proposition;
    let mut negative = false;
    while let Proposition::Not(body) = proposition {
        negative = !negative;
        proposition = body;
    }
    let Proposition::ConditionIs(condition, truth) = proposition else {
        return None;
    };
    let truth = *truth != negative;
    if matches!(condition, ConditionTerm::Compare { .. }) {
        let observed =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                &Proposition::ConditionIs(condition.clone(), truth),
            )
            .into_iter()
            .next()?;
        return reading(&observed);
    }
    let (a, b, equal, strict, reverse) = match (condition, truth) {
        (ConditionTerm::IntegerEqual(a, b), true)
        | (ConditionTerm::IntegerNotEqual(a, b), false) => (a, b, true, false, false),
        (ConditionTerm::IntegerLessEqual(a, b), true)
        | (ConditionTerm::IntegerGreaterThan(a, b), false) => (a, b, false, false, false),
        (ConditionTerm::IntegerGreaterEqual(a, b), true)
        | (ConditionTerm::IntegerLessThan(a, b), false) => (a, b, false, false, true),
        (ConditionTerm::IntegerLessThan(a, b), true)
        | (ConditionTerm::IntegerGreaterEqual(a, b), false) => (a, b, false, true, false),
        (ConditionTerm::IntegerGreaterThan(a, b), true)
        | (ConditionTerm::IntegerLessEqual(a, b), false) => (a, b, false, true, true),
        _ => return None,
    };
    Some(Reading {
        left: if reverse { b.clone() } else { a.clone() },
        right: if reverse { a.clone() } else { b.clone() },
        equal,
        strict,
    })
}

fn canonical_surface(surface: &ClickProposition) -> Option<ClickProposition> {
    let anchored = surface_comparison_with_anchored_operands(surface);
    let mut surface = &anchored;
    let mut negative = false;
    while let ClickProposition::Not(body) = surface {
        negative = !negative;
        surface = body;
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = surface
    else {
        return None;
    };
    let operator = if negative {
        match operator {
            ComparisonOperator::Equal => ComparisonOperator::NotEqual,
            ComparisonOperator::NotEqual => ComparisonOperator::Equal,
            ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
            ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
            ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
            ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
            _ => return None,
        }
    } else {
        *operator
    };
    let (left, operator, right) = match operator {
        ComparisonOperator::GreaterEqual => {
            (right.clone(), ComparisonOperator::LessEqual, left.clone())
        }
        ComparisonOperator::GreaterThan => {
            (right.clone(), ComparisonOperator::LessThan, left.clone())
        }
        operator => (left.clone(), operator, right.clone()),
    };
    Some(ClickProposition::Comparison {
        left,
        operator,
        right,
    })
}

fn prepare_relation(
    relation: Reading,
    canonical: &ClickProposition,
    source: &ClickProposition,
    atoms: &mut BTreeMap<u64, Atom>,
) -> (Form, bool, Vec<ProofStep>) {
    let (mut left, _, right) = integer_surface_ordered_parts(canonical).expect("ordered source");
    let mut form = operand(&relation.left, left.clone(), atoms)
        .add(&operand(&relation.right, right.clone(), atoms).scaled(&BigInt::from(-1)));
    let mut body = Vec::new();
    let mut ordered = canonical.clone();
    if &ordered != source {
        body.push(have(ordered.clone(), vec![ProofStep::Known]));
    }
    if relation.strict {
        form.constant += 1;
        let shifted = compare(
            add(left.clone(), literal(&BigInt::one())),
            false,
            right.clone(),
        );
        body.push(have(
            shifted.clone(),
            vec![application(
                "lt_step_le",
                vec![left.clone(), right.clone()],
                vec![ordered],
            )],
        ));
        left = add(left, literal(&BigInt::one()));
        ordered = shifted;
    }
    let target = compare(expression(&form, atoms), relation.equal, zero());
    if !relation.equal {
        let value = expression(&form, atoms);
        let identity = compare(
            value.clone(),
            true,
            ContractExpression::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        );
        body.push(arithmetic_identity(identity.clone()));
        body.push(application(
            "le_difference",
            vec![left, right, value],
            vec![ordered, identity],
        ));
        return (form, false, body);
    }

    let shifted = compare(
        ContractExpression::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        true,
        zero(),
    );
    body.push(have(
        shifted.clone(),
        vec![application(
            "equal_difference",
            vec![left, right],
            vec![ordered],
        )],
    ));
    body.extend(transfer(&target, &shifted));
    (form, relation.equal, body)
}

fn restore(target: &ClickProposition, node: &Node, atoms: &BTreeMap<u64, Atom>) -> Vec<ProofStep> {
    let (_, operator, right) = integer_surface_non_strict_parts(target).expect("ordered target");
    let equal = operator == ComparisonOperator::Equal;
    if !equal {
        let (left, _, right) = integer_surface_non_strict_parts(target).expect("ordered target");
        let value = expression(&node.form, atoms);
        let identity = compare(
            value.clone(),
            true,
            ContractExpression::Subtract(Box::new(left.clone()), Box::new(right.clone())),
        );
        return vec![
            arithmetic_identity(identity.clone()),
            application(
                "difference_le",
                vec![left, right, value],
                vec![node.claim.clone(), identity],
            ),
        ];
    }
    let value = expression(&node.form, atoms);
    let reflexive = compare(right.clone(), equal, right.clone());
    let fact = compare(
        add(value.clone(), right.clone()),
        equal,
        add(zero(), right.clone()),
    );
    let mut body = vec![have(
        fact.clone(),
        vec![application(
            if equal { "equal_add" } else { "add_le" },
            vec![value, zero(), right.clone(), right],
            vec![node.claim.clone(), reflexive],
        )],
    )];
    let (left, _, right) = integer_surface_non_strict_parts(target).expect("ordered target");
    let non_strict = compare(left, equal, right);
    body.extend(transfer(&non_strict, &fact));
    body
}

fn disequality_operands(proposition: &Proposition) -> Vec<(SharedIntegerTerm, SharedIntegerTerm)> {
    let mut p = proposition;
    let mut negative = false;
    while let Proposition::Not(body) = p {
        negative = !negative;
        p = body;
    }
    let Proposition::ConditionIs(c, v) = p else {
        return Vec::new();
    };
    if matches!(c, ConditionTerm::Compare { .. }) {
        return crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::ConditionIs(c.clone(), *v != negative),
        )
        .iter()
        .flat_map(disequality_operands)
        .collect();
    }
    match (c, *v != negative) {
        (ConditionTerm::IntegerNotEqual(a, b), true)
        | (ConditionTerm::IntegerEqual(a, b), false) => vec![(a.clone(), b.clone())],
        _ => Vec::new(),
    }
}

fn strict_node(
    proof: &Proof<'_>,
    bound: &Node,
    disequal: &(Proposition, ClickProposition),
    atoms: &mut BTreeMap<u64, Atom>,
) -> Result<(Form, bool, Vec<ProofStep>), ClickError> {
    let observed = observed_native_surface_comparison(&disequal.0, &disequal.1);
    let lowered = proof.lower_cited_surface_proposition(&observed, "Integer disequality")?;
    let (a, b, reverse) = disequality_operands(&lowered)
        .into_iter()
        .find_map(|(a, b)| {
            for reverse in [false, true] {
                let (left, right) = if reverse { (&b, &a) } else { (&a, &b) };
                let forward = Proposition::ConditionIs(
                    ConditionTerm::IntegerLessEqual(left.clone(), right.clone()),
                    true,
                );
                if integer_affine_claim(&forward).as_ref() == Some(&bound.semantic) {
                    return Some(if reverse { (b, a, true) } else { (a, b, false) });
                }
            }
            None
        })
        .ok_or_else(|| proof.step_error("Integer strictness requires its bound's disequality"))?;
    let canonical = canonical_surface(&observed)
        .ok_or_else(|| proof.step_error("Integer disequality has no comparison spelling"))?;
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::NotEqual,
        right,
    } = canonical
    else {
        return Err(proof.step_error("Integer strictness requires a disequality spelling"));
    };
    let (mut left, mut right) = (left, right);
    if reverse {
        std::mem::swap(&mut left, &mut right);
    }
    let ordered = compare(left.clone(), false, right.clone());
    let neq = ClickProposition::Comparison {
        left: left.clone(),
        operator: ComparisonOperator::NotEqual,
        right: right.clone(),
    };
    let strict = ClickProposition::Comparison {
        left: left.clone(),
        operator: ComparisonOperator::LessThan,
        right: right.clone(),
    };
    let mut body = vec![
        have(ordered.clone(), restore(&ordered, bound, atoms)),
        have(neq.clone(), vec![ProofStep::Known]),
        have(
            strict.clone(),
            vec![application(
                "le_ne_lt",
                vec![left, right],
                vec![ordered, neq],
            )],
        ),
    ];
    let (form, equal, tail) = prepare_relation(
        Reading {
            left: a,
            right: b,
            equal: false,
            strict: true,
        },
        &strict,
        &strict,
        atoms,
    );
    body.extend(tail);
    Ok((form, equal, body))
}

// When a linear refutation uses the negated goal once, cancel that
// assumption in the plan itself. The remaining selected facts prove the
// goal directly; there is no reason to construct a double-negation proof.
fn direct_refutation(
    plan: &IntegerArithmeticCertificate,
    goal: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if goal.relation != IntegerAffineRelation::LessEqual
        || !contradiction_claim(node_claim(plan.nodes.get(plan.conclusion)?))
    {
        return None;
    }
    let mut weights: Vec<BigInt> = Vec::with_capacity(plan.nodes.len());
    let mut negated = None;
    for node in &plan.nodes {
        crate::instrumentation::record_deterministic_work(1);
        let weight = match node {
            IntegerArithmeticNode::NegatedGoal { result } => {
                if negated.replace(result.clone()).is_some() {
                    return None;
                }
                BigInt::one()
            }
            IntegerArithmeticNode::Scale {
                source,
                coefficient,
                ..
            } => {
                let weight = weights.get(*source)?;
                if crate::instrumentation::deadline_exceeded_with_work(
                    (weight.bits() as usize + 1).saturating_mul(coefficient.bits() as usize + 1),
                ) {
                    return None;
                }
                weight * coefficient
            }
            IntegerArithmeticNode::Add { left, right, .. } => {
                weights.get(*left)? + weights.get(*right)?
            }
            IntegerArithmeticNode::EqualityToLessEqual {
                source, reverse, ..
            } => {
                let weight = weights.get(*source)?.clone();
                if *reverse { -weight } else { weight }
            }
            IntegerArithmeticNode::Premise { .. }
            | IntegerArithmeticNode::TypeRange { .. }
            | IntegerArithmeticNode::OperationBound { .. }
            | IntegerArithmeticNode::ExcludedTypeBound { .. }
            | IntegerArithmeticNode::Trivial { .. } => BigInt::zero(),
            _ => return None,
        };
        weights.push(weight);
    }
    if !weights.get(plan.conclusion)?.is_one() {
        return None;
    }
    let negated = negated?;
    let mut mapping = Vec::with_capacity(plan.nodes.len());
    let mut nodes = Vec::with_capacity(plan.nodes.len());
    for (index, node) in plan.nodes.iter().enumerate() {
        let mut result = node_claim(node).clone();
        for (atom, coefficient) in &negated.terms {
            if crate::instrumentation::deadline_exceeded_with_work(
                (coefficient.bits() as usize + 1)
                    .saturating_mul(weights[index].bits() as usize + 1),
            ) {
                return None;
            }
            *result.terms.entry(atom.clone()).or_default() -= coefficient * &weights[index];
        }
        result.terms.retain(|_, coefficient| !coefficient.is_zero());
        result.constant -= &negated.constant * &weights[index];
        let new_node = match node {
            IntegerArithmeticNode::NegatedGoal { .. } => {
                mapping.push(None);
                continue;
            }
            IntegerArithmeticNode::Scale {
                source,
                coefficient,
                ..
            } => {
                let Some(source) = mapping[*source] else {
                    mapping.push(None);
                    continue;
                };
                IntegerArithmeticNode::Scale {
                    source,
                    coefficient: coefficient.clone(),
                    result,
                }
            }
            IntegerArithmeticNode::Add { left, right, .. } => {
                match (mapping[*left], mapping[*right]) {
                    (Some(left), Some(right)) => IntegerArithmeticNode::Add {
                        left,
                        right,
                        result,
                    },
                    (left, right) => {
                        mapping.push(left.or(right));
                        continue;
                    }
                }
            }
            IntegerArithmeticNode::EqualityToLessEqual {
                source, reverse, ..
            } => {
                let Some(source) = mapping[*source] else {
                    mapping.push(None);
                    continue;
                };
                IntegerArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse: *reverse,
                    result,
                }
            }
            other => other.clone(),
        };
        mapping.push(Some(nodes.len()));
        nodes.push(new_node);
    }
    let mut conclusion = mapping[plan.conclusion]?;
    let actual = node_claim(&nodes[conclusion]);
    if actual.terms != goal.terms || actual.relation != goal.relation {
        return None;
    }
    let slack = &actual.constant - &goal.constant;
    if slack.is_negative() {
        return None;
    }
    if !slack.is_zero() {
        let trivial = nodes.len();
        nodes.push(IntegerArithmeticNode::Trivial {
            result: IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms: BTreeMap::new(),
                constant: -slack,
            },
        });
        nodes.push(IntegerArithmeticNode::Add {
            left: conclusion,
            right: trivial,
            result: goal.clone(),
        });
        conclusion = nodes.len() - 1;
    }
    Some(IntegerArithmeticCertificate { nodes, conclusion })
}

fn node_claim(node: &IntegerArithmeticNode) -> &IntegerAffineClaim {
    match node {
        IntegerArithmeticNode::Premise { result, .. }
        | IntegerArithmeticNode::Scale { result, .. }
        | IntegerArithmeticNode::Add { result, .. }
        | IntegerArithmeticNode::EqualityToLessEqual { result, .. }
        | IntegerArithmeticNode::EqualityFromBounds { result, .. }
        | IntegerArithmeticNode::Trivial { result }
        | IntegerArithmeticNode::NegatedGoal { result }
        | IntegerArithmeticNode::Divide { result, .. }
        | IntegerArithmeticNode::TypeRange { result, .. }
        | IntegerArithmeticNode::OperationBound { result, .. }
        | IntegerArithmeticNode::ExcludedTypeBound { result, .. }
        | IntegerArithmeticNode::StrictFromDisequal { result, .. } => result,
    }
}

fn contradiction_claim(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant > BigInt::zero(),
            IntegerAffineRelation::Equal => !claim.constant.is_zero(),
        }
}

/// Restate one relation by explicitly proved identities of its operands.
/// There is no affine reasoning over facts hidden in `normalize using`:
/// all the algebra is in the two context-free identity goals.
fn transfer(target: &ClickProposition, fact: &ClickProposition) -> Vec<ProofStep> {
    let (a, operator, b) = integer_surface_ordered_parts(target).expect("composition target");
    let (c, _, d) = integer_surface_ordered_parts(fact).expect("composition fact");
    let left = compare(a.clone(), true, c.clone());
    let right = compare(b.clone(), true, d.clone());
    let mut body = Vec::new();
    if a != c {
        body.push(arithmetic_identity(left.clone()));
    }
    if b != d {
        body.push(arithmetic_identity(right.clone()));
    }
    body.push(application(
        if operator == ComparisonOperator::Equal {
            "equal_substitute"
        } else {
            "le_substitute"
        },
        vec![c, d, a, b],
        vec![fact.clone(), left, right],
    ));
    body
}

fn with_argument_domains(step: ProofStep, domains: &[ClickProposition]) -> ProofStep {
    match step {
        ProofStep::Have { proposition, proof } => have(
            proposition,
            proof
                .steps()
                .iter()
                .cloned()
                .map(|step| with_argument_domains(step, domains))
                .collect(),
        ),
        ProofStep::ApplyTheoremUsing {
            application,
            mut premises,
        } => {
            premises.extend(
                domains
                    .iter()
                    .filter(|domain| !premises.contains(domain))
                    .cloned()
                    .collect::<Vec<_>>(),
            );
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            }
        }
        other => other,
    }
}

pub(super) fn observed_argument(expression: &ContractExpression) -> Option<ContractExpression> {
    match expression {
        ContractExpression::Call { name, arguments }
            if name == "to_integer" && arguments.len() == 1 =>
        {
            observed_argument(&arguments[0]).or_else(|| Some(arguments[0].clone()))
        }
        ContractExpression::At {
            selector,
            expression,
        } => Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(observed_argument(expression)?),
        }),
        ContractExpression::Old(expression) => Some(ContractExpression::Old(Box::new(
            observed_argument(expression)?,
        ))),
        ContractExpression::Let {
            name,
            click_type: Some(ClickType::Integer),
            value,
            body,
        } if matches!(body.as_ref(), ContractExpression::Binding(bound) if bound == name) => {
            observed_argument(value)
        }
        _ => None,
    }
}

fn run_scope<'a>(
    mut scope: super::super::proof_object::ProofScope<'a>,
    steps: &[ProofStep],
) -> Result<super::super::proof_object::ProofScope<'a>, ClickError> {
    for step in steps {
        if scope.is_complete() {
            break;
        }
        match step {
            ProofStep::Have { proposition, proof } => {
                let nested = scope.driver().open_have(proposition.clone())?;
                let closed = run_scope(nested, proof.steps())?;
                scope = scope.join_nested(closed)?;
            }
            step => scope = scope.driver().apply_step(step.clone())?,
        }
    }
    Ok(scope)
}

#[cfg(test)]
thread_local! {
    static LAST_FAILURE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
pub(super) fn note_refusal(message: impl Into<String>) {
    LAST_FAILURE.with(|failure| *failure.borrow_mut() = Some(message.into()));
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn apply_integer_composition(
        proof: &Proof<'a>,
        plan: &IntegerArithmeticCertificate,
        pairs: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
        ranges: &[SpelledBound],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_integer_composition");
        let Some(goal) = proof.goal() else {
            return Ok(None);
        };
        #[cfg(test)]
        note_refusal("entered composition construction");
        let observed_goal = observed_native_surface_comparison(goal, surface_goal);
        let goal_kernel =
            proof.lower_cited_surface_proposition(&observed_goal, "Integer composition goal")?;
        let goal_reading = reading(&goal_kernel);
        let goal_surface = canonical_surface(&observed_goal);
        let Some(expected) = integer_affine_claim(&goal_kernel) else {
            return Ok(None);
        };
        let direct = direct_refutation(plan, &expected);
        let plan = direct.as_ref().unwrap_or(plan);
        let contradictory = contradiction_claim(node_claim(&plan.nodes[plan.conclusion]));
        if node_claim(&plan.nodes[plan.conclusion]) != &expected && !contradictory {
            #[cfg(test)]
            LAST_FAILURE.with(|failure| {
                *failure.borrow_mut() = Some(format!(
                    "plan result {:?}, observed goal {:?}",
                    node_claim(&plan.nodes[plan.conclusion]),
                    expected
                ))
            });
            return Ok(None);
        }
        let mut uses_negated_goal = false;
        let mut used = BTreeSet::new();
        let mut pending = vec![plan.conclusion];
        while let Some(index) = pending.pop() {
            if !used.insert(index) {
                continue;
            }
            let Some(node) = plan.nodes.get(index) else {
                return Ok(None);
            };
            match node {
                IntegerArithmeticNode::Premise { index, .. } => {
                    if pairs.get(*index).is_none() {
                        return Ok(None);
                    }
                }
                IntegerArithmeticNode::Scale { source, .. }
                | IntegerArithmeticNode::EqualityToLessEqual { source, .. } => {
                    pending.push(*source)
                }
                IntegerArithmeticNode::Add { left, right, .. } => pending.extend([*left, *right]),
                IntegerArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                    pending.extend([*lower, *upper])
                }
                IntegerArithmeticNode::StrictFromDisequal { bound, .. } => pending.push(*bound),
                IntegerArithmeticNode::NegatedGoal { .. } => uses_negated_goal = true,
                IntegerArithmeticNode::Divide { source, .. } => pending.push(*source),
                _ => {}
            }
        }
        let owned_ranges;
        let ranges = if ranges.is_empty()
            && used.iter().any(|index| {
                matches!(
                    plan.nodes[*index],
                    IntegerArithmeticNode::TypeRange { .. }
                        | IntegerArithmeticNode::OperationBound { .. }
                        | IntegerArithmeticNode::ExcludedTypeBound { .. }
                )
            }) {
            let written = written_integer_observations(
                std::iter::once(surface_goal).chain(pairs.iter().map(|(_, surface)| surface)),
            );
            let mut spelled = proof
                .spell_type_ranges(plan, &written)
                .map_err(|_| proof.step_error("Integer type range has no source spelling"))?;
            let kernels = pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            spelled.extend(
                proof
                    .spell_derived_bounds(plan, &kernels, &written)
                    .ok_or_else(|| {
                        proof.step_error("Integer operation bound has no source spelling")
                    })?,
            );
            owned_ranges = spelled;
            owned_ranges.as_slice()
        } else {
            ranges
        };
        let mut atoms = BTreeMap::new();
        let mut nodes: BTreeMap<usize, Node> = BTreeMap::new();
        let mut steps = Vec::new();
        for index in used {
            check_verification_deadline()?;
            let (form, equal, body) = match &plan.nodes[index] {
                IntegerArithmeticNode::Premise { index, .. } => {
                    let (kernel, source) = &pairs[*index];
                    let observed = observed_native_surface_comparison(kernel, source);
                    let lowered = proof.lower_cited_surface_proposition(
                        &observed,
                        "Integer composition premise",
                    )?;
                    let Some(relation) = reading(&lowered) else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&observed) else {
                        return Ok(None);
                    };
                    prepare_relation(relation, &canonical, source, &mut atoms)
                }
                IntegerArithmeticNode::NegatedGoal { .. } => {
                    let source = ClickProposition::Not(Box::new(surface_goal.clone()));
                    let kernel = Proposition::Not(Box::new(goal.clone()));
                    let observed = observed_native_surface_comparison(&kernel, &source);
                    let lowered =
                        proof.lower_cited_surface_proposition(&observed, "Integer negated goal")?;
                    let Some(relation) = reading(&lowered) else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&observed) else {
                        return Ok(None);
                    };
                    prepare_relation(relation, &canonical, &source, &mut atoms)
                }
                IntegerArithmeticNode::TypeRange { value, upper, .. }
                | IntegerArithmeticNode::OperationBound { value, upper, .. } => {
                    let kind =
                        if matches!(&plan.nodes[index], IntegerArithmeticNode::TypeRange { .. }) {
                            BoundSource::TypeRange
                        } else {
                            BoundSource::Operation
                        };
                    let Some(source) = spelled_bound(ranges, kind, value, *upper) else {
                        return Ok(None);
                    };
                    let lowered = proof
                        .lower_cited_surface_proposition(&source, "Integer intrinsic bound")?;
                    let Some(relation) = reading(&lowered) else {
                        #[cfg(test)]
                        note_refusal(format!("unsupported observed source: {lowered:?}"));
                        return Ok(None);
                    };
                    let Some(canonical) = canonical_surface(&source) else {
                        return Ok(None);
                    };
                    let (form, equal, mut body) =
                        prepare_relation(relation, &canonical, &source, &mut atoms);
                    let node = match kind {
                        BoundSource::TypeRange => IntegerCertificateNode::TypeRange {
                            result: source.clone(),
                        },
                        BoundSource::Operation => IntegerCertificateNode::OperationBound {
                            result: source.clone(),
                        },
                        _ => unreachable!("intrinsic bound kind"),
                    };
                    body.insert(
                        0,
                        have(
                            source,
                            vec![ProofStep::ArithmeticCertificate(
                                ArithmeticCertificate::integer(IntegerCertificate {
                                    nodes: vec![node],
                                    conclusion: 0,
                                }),
                            )],
                        ),
                    );
                    (form, equal, body)
                }
                IntegerArithmeticNode::StrictFromDisequal {
                    bound, disequal, ..
                } => strict_node(proof, &nodes[bound], &pairs[*disequal], &mut atoms)?,
                IntegerArithmeticNode::ExcludedTypeBound { index: premise, .. } => {
                    let source = ranges
                        .iter()
                        .find(|(kind, ..)| *kind == BoundSource::Excluded(*premise))
                        .map(|(.., surface)| surface)
                        .ok_or_else(|| proof.step_error("excluded type bound has no spelling"))?;
                    let kernel =
                        proof.lower_cited_surface_proposition(source, "excluded type bound")?;
                    let relation = reading(&kernel).expect("excluded bound is ordered");
                    let (left, _, right) =
                        integer_surface_ordered_parts(source).expect("excluded bound spelling");
                    let (base_kernel, base_surface) =
                        if let Some(min_plus_one) = relation.left.as_const() {
                            let min = min_plus_one - BigInt::one();
                            (
                                Proposition::ConditionIs(
                                    ConditionTerm::IntegerLessEqual(
                                        IntegerTerm::constant(min.clone()).into(),
                                        relation.right,
                                    ),
                                    true,
                                ),
                                compare(literal(&min), false, right),
                            )
                        } else {
                            let max =
                                relation.right.as_const().expect("upper endpoint") + BigInt::one();
                            (
                                Proposition::ConditionIs(
                                    ConditionTerm::IntegerLessEqual(
                                        relation.left,
                                        IntegerTerm::constant(max.clone()).into(),
                                    ),
                                    true,
                                ),
                                compare(left, false, literal(&max)),
                            )
                        };
                    let (form, equal, mut base_body) = prepare_relation(
                        reading(&base_kernel).unwrap(),
                        &base_surface,
                        &base_surface,
                        &mut atoms,
                    );
                    base_body.insert(
                        0,
                        have(
                            base_surface.clone(),
                            vec![ProofStep::ArithmeticCertificate(
                                ArithmeticCertificate::integer(IntegerCertificate {
                                    nodes: vec![IntegerCertificateNode::TypeRange {
                                        result: base_surface,
                                    }],
                                    conclusion: 0,
                                }),
                            )],
                        ),
                    );
                    let base_claim = compare(expression(&form, &atoms), false, zero());
                    let base = Node {
                        form,
                        equal,
                        claim: base_claim.clone(),
                        semantic: integer_affine_claim(&base_kernel).unwrap(),
                    };
                    let (form, equal, mut body) =
                        strict_node(proof, &base, &pairs[*premise], &mut atoms)?;
                    body.insert(0, have(base_claim, base_body));
                    (form, equal, body)
                }
                IntegerArithmeticNode::Divide {
                    source,
                    divisor,
                    result: semantic,
                } => {
                    if divisor <= &BigInt::zero() {
                        return Err(proof.step_error("Integer rounding needs a positive divisor"));
                    }
                    let source = &nodes[source];
                    let form = if index == plan.conclusion {
                        let (Some(relation), Some(canonical)) = (&goal_reading, &goal_surface)
                        else {
                            return Ok(None);
                        };
                        let (left, _, right) =
                            integer_surface_ordered_parts(canonical).expect("rounding target");
                        let mut form = operand(&relation.left, left, &mut atoms).add(
                            &operand(&relation.right, right, &mut atoms).scaled(&BigInt::from(-1)),
                        );
                        if relation.strict {
                            form.constant += 1;
                        }
                        form
                    } else {
                        if source
                            .form
                            .terms
                            .values()
                            .any(|coefficient| !(coefficient % divisor).is_zero())
                        {
                            return Ok(None);
                        }
                        let mut constant = &source.form.constant / divisor;
                        if &source.form.constant % divisor > BigInt::zero() {
                            constant += 1;
                        }
                        Form {
                            terms: source
                                .form
                                .terms
                                .iter()
                                .map(|(key, coefficient)| (*key, coefficient / divisor))
                                .collect(),
                            constant,
                        }
                    };
                    let remainder = divisor * &semantic.constant - &source.semantic.constant;
                    let factor = literal(divisor);
                    let slack = literal(&remainder);
                    let positive = ClickProposition::Comparison {
                        left: expression(&Form::default(), &atoms),
                        operator: ComparisonOperator::LessThan,
                        right: factor.clone(),
                    };
                    let small = ClickProposition::Comparison {
                        left: expression(
                            &Form {
                                constant: remainder.clone(),
                                ..Form::default()
                            },
                            &atoms,
                        ),
                        operator: ComparisonOperator::LessThan,
                        right: factor.clone(),
                    };
                    let reflexive = compare(slack.clone(), false, slack.clone());
                    let raw = compare(
                        add(expression(&source.form, &atoms), slack.clone()),
                        false,
                        add(zero(), slack.clone()),
                    );
                    let value = expression(&form, &atoms);
                    let shifted = compare(
                        multiply(value.clone(), factor.clone()),
                        false,
                        add(multiply(zero(), factor.clone()), slack.clone()),
                    );
                    let body = vec![
                        arithmetic_identity(positive.clone()),
                        arithmetic_identity(small.clone()),
                        arithmetic_identity(reflexive.clone()),
                        have(
                            raw.clone(),
                            vec![application(
                                "add_le",
                                vec![
                                    expression(&source.form, &atoms),
                                    zero(),
                                    slack.clone(),
                                    slack.clone(),
                                ],
                                vec![source.claim.clone(), reflexive],
                            )],
                        ),
                        have(shifted.clone(), transfer(&shifted, &raw)),
                        application(
                            "round_down_le",
                            vec![value, zero(), factor, slack],
                            vec![positive, small, shifted],
                        ),
                    ];
                    (form, false, body)
                }
                IntegerArithmeticNode::Scale {
                    source,
                    coefficient,
                    ..
                } => {
                    let source = &nodes[source];
                    let form = source.form.scaled(coefficient);
                    let factor = literal(coefficient);
                    let raw = multiply(expression(&source.form, &atoms), factor.clone());
                    let target = compare(expression(&form, &atoms), source.equal, zero());
                    let mut body = Vec::new();
                    let fact = if source.equal {
                        let fact = compare(raw, true, multiply(zero(), factor.clone()));
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "equal_multiply",
                                vec![expression(&source.form, &atoms), zero(), factor.clone()],
                                vec![source.claim.clone()],
                            )],
                        ));
                        fact
                    } else {
                        let positive = compare(zero(), false, factor.clone());
                        body.push(arithmetic_identity(positive.clone()));
                        let fact = compare(raw, false, multiply(zero(), factor.clone()));
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "multiply_order_nonnegative",
                                vec![expression(&source.form, &atoms), zero(), factor],
                                vec![source.claim.clone(), positive],
                            )],
                        ));
                        fact
                    };
                    body.extend(transfer(&target, &fact));
                    (form, source.equal, body)
                }
                IntegerArithmeticNode::Add { left, right, .. } => {
                    let (left, right) = (&nodes[left], &nodes[right]);
                    let form = left.form.add(&right.form);
                    let raw = add(
                        expression(&left.form, &atoms),
                        expression(&right.form, &atoms),
                    );
                    let target = compare(expression(&form, &atoms), left.equal, zero());
                    let fact = compare(raw, left.equal, add(zero(), zero()));
                    let body = if left.equal {
                        vec![application(
                            "equal_add",
                            vec![
                                expression(&left.form, &atoms),
                                zero(),
                                expression(&right.form, &atoms),
                                zero(),
                            ],
                            vec![left.claim.clone(), right.claim.clone()],
                        )]
                    } else {
                        vec![application(
                            "add_le",
                            vec![
                                expression(&left.form, &atoms),
                                zero(),
                                expression(&right.form, &atoms),
                                zero(),
                            ],
                            vec![left.claim.clone(), right.claim.clone()],
                        )]
                    };
                    let mut body = vec![have(fact.clone(), body)];
                    body.extend(transfer(&target, &fact));
                    (form, left.equal, body)
                }
                IntegerArithmeticNode::EqualityToLessEqual {
                    source, reverse, ..
                } => {
                    let source = &nodes[source];
                    let form = source
                        .form
                        .scaled(&BigInt::from(if *reverse { -1 } else { 1 }));
                    let value = expression(&form, &atoms);
                    let equal = compare(value.clone(), true, zero());
                    let mut body = Vec::new();
                    if *reverse {
                        let factor = literal(&BigInt::from(-1));
                        let fact = compare(
                            multiply(expression(&source.form, &atoms), factor.clone()),
                            true,
                            multiply(zero(), factor.clone()),
                        );
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "equal_multiply",
                                vec![expression(&source.form, &atoms), zero(), factor],
                                vec![source.claim.clone()],
                            )],
                        ));
                        body.push(have(equal.clone(), transfer(&equal, &fact)));
                    }
                    body.push(application("equal_le", vec![value, zero()], vec![equal]));
                    (form, false, body)
                }
                IntegerArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                    let (lower, upper) = (&nodes[lower], &nodes[upper]);
                    let form = lower.form.clone();
                    let value = expression(&form, &atoms);
                    let reflexive = compare(value.clone(), false, value.clone());
                    let fact = compare(
                        add(expression(&upper.form, &atoms), value.clone()),
                        false,
                        add(zero(), value.clone()),
                    );
                    let opposite = compare(zero(), false, value.clone());
                    let mut body = vec![
                        arithmetic_identity(reflexive.clone()),
                        have(
                            fact.clone(),
                            vec![application(
                                "add_le",
                                vec![
                                    expression(&upper.form, &atoms),
                                    zero(),
                                    value.clone(),
                                    value.clone(),
                                ],
                                vec![upper.claim.clone(), reflexive],
                            )],
                        ),
                    ];
                    body.push(have(opposite.clone(), transfer(&opposite, &fact)));
                    body.push(application(
                        "le_antisymmetric",
                        vec![value, zero()],
                        vec![lower.claim.clone(), opposite],
                    ));
                    (form, true, body)
                }
                IntegerArithmeticNode::Trivial { result } => (
                    Form {
                        constant: result.constant.clone(),
                        ..Form::default()
                    },
                    result.relation == IntegerAffineRelation::Equal,
                    vec![trivial_arithmetic_step(compare(
                        literal(&result.constant),
                        result.relation == IntegerAffineRelation::Equal,
                        zero(),
                    ))],
                ),
            };
            let claim = compare(expression(&form, &atoms), equal, zero());
            steps.push(have(claim.clone(), body));
            nodes.insert(
                index,
                Node {
                    form,
                    equal,
                    claim,
                    semantic: node_claim(&plan.nodes[index]).clone(),
                },
            );
        }
        let conclusion = &nodes[&plan.conclusion];
        if contradictory {
            steps.push(ProofStep::Contradiction(conclusion.claim.clone()));
        } else {
            let (Some(relation), Some(canonical)) = (goal_reading, goal_surface) else {
                return Ok(None);
            };
            let (left, _, right) =
                integer_surface_non_strict_parts(&canonical).expect("ordered goal");
            let non_strict = compare(left, relation.equal, right);
            steps.extend(restore(&canonical, conclusion, &atoms));
            if relation.strict {
                let (left, _, right) =
                    integer_surface_ordered_parts(&canonical).expect("strict goal");
                steps.push(application(
                    "step_le_lt",
                    vec![left, right],
                    vec![non_strict],
                ));
            }
            if uses_negated_goal {
                steps.push(ProofStep::Contradiction(surface_goal.clone()));
            } else {
                steps = vec![have(canonical.clone(), steps), ProofStep::Known];
            }
        }
        if uses_negated_goal {
            let double_negation = ClickProposition::Not(Box::new(ClickProposition::Not(Box::new(
                surface_goal.clone(),
            ))));
            steps.insert(0, ProofStep::Intro);
            steps = vec![have(double_negation.clone(), steps), ProofStep::Known];
        }
        // The theorem's arguments can contain partial native operations.
        // Cite their already established domains explicitly, so the simple
        // using checker sees the same argument evidence during replay.
        let written = written_integer_observations(
            std::iter::once(surface_goal).chain(pairs.iter().map(|(_, surface)| surface)),
        );
        let mut domains = Vec::new();
        let mut domain_proofs = Vec::new();
        for expression in &written {
            let Some(expression) = observed_argument(expression) else {
                continue;
            };
            let domain = ClickProposition::Defined { expression };
            // Synthetic observations of an Integer are not native domains.
            let Ok(kernel) =
                proof.lower_cited_surface_proposition(&domain, "Integer argument domain")
            else {
                continue;
            };
            let Some(query) =
                crate::kernel::machine_integer::definedness::range_domain_query(&kernel)
            else {
                // Reads can carry a separate domain as well. Retain that
                // exact established fact for theorem-argument checking.
                if !normalizes_context_free(&kernel)
                    && proof.facts().listed_premise_available(&kernel, &[], false)
                    && !domains.contains(&domain)
                {
                    domain_proofs.push(have(domain.clone(), vec![ProofStep::Known]));
                    domains.push(domain);
                }
                continue;
            };
            if domains.contains(&domain) {
                continue;
            }
            if proof.facts().listed_premise_available(&kernel, &[], false) {
                domain_proofs.push(have(domain.clone(), vec![ProofStep::Known]));
            } else if query
                .bounds()
                .iter()
                .all(|bound| proof.facts().listed_premise_available(bound, &[], false))
            {
                domain_proofs.push(have(
                    domain.clone(),
                    vec![ProofStep::Both {
                        left_proof: Box::new(ProofCertificate::from_validated_steps(vec![
                            ProofStep::Known,
                        ])),
                        right_proof: Box::new(ProofCertificate::from_validated_steps(vec![
                            ProofStep::Known,
                        ])),
                    }],
                ));
            } else {
                continue;
            }
            domains.push(domain);
        }
        if !domains.is_empty() {
            domain_proofs.extend(
                steps
                    .into_iter()
                    .map(|step| with_argument_domains(step, &domains)),
            );
            steps = domain_proofs;
        }
        let mut result = proof.clone();
        for step in steps {
            if result.focused_discharged() {
                break;
            }
            let next = match step {
                ProofStep::Have { proposition, proof } => {
                    let scope = result.driver().open_have(proposition)?;
                    run_scope(scope, proof.steps()).and_then(|scope| scope.join())
                }
                step => result.driver().apply_step(step),
            };
            #[cfg(test)]
            if let Err(error) = &next {
                LAST_FAILURE
                    .with(|failure| *failure.borrow_mut() = Some(error.raw_summary().to_owned()));
            }
            result = next?;
        }
        if !result.focused_discharged() {
            return Err(result.step_error("Integer composition did not close the written goal"));
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    use super::*;
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    use crate::surface::proof::pure_theorems::PureTheoremContext;

    pub(super) fn shared_plan(
        depth: usize,
        ambient: usize,
        related: bool,
    ) -> (usize, usize, usize) {
        let x: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_001)).into();
        let y: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_002)).into();
        let z: SharedIntegerTerm = IntegerTerm::Variable(Variable(871_003)).into();
        let premise =
            Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(x.clone(), y.clone()), true);
        let surface = compare(
            ContractExpression::Binding("x".into()),
            false,
            ContractExpression::Binding("y".into()),
        );
        let mut context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            memory: Memory::new(),
            values: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            array_refs: BTreeMap::new(),
            requires: vec![premise.clone()],
            surface_requirements: SurfacePropositionMap::default(),
        };
        for (name, term) in [("x", &x), ("y", &y), ("z", &z)] {
            context.integer_values = context.integer_values.with_inserted(
                name.into(),
                SpecIntegerExpression::Term(term.as_ref().clone()),
            );
        }
        for index in 1..=ambient {
            context.requires.push(Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    if related { x.clone() } else { z.clone() },
                    if related {
                        IntegerTerm::add(
                            y.as_ref().clone(),
                            IntegerTerm::constant_i64(index as i64),
                        )
                        .into()
                    } else {
                        IntegerTerm::constant_i64(index as i64).into()
                    },
                ),
                true,
            ));
        }
        let mut claim = integer_affine_claim(&premise).unwrap();
        let mut nodes = vec![IntegerArithmeticNode::Premise {
            index: 0,
            result: claim.clone(),
        }];
        for source in 0..depth {
            for coefficient in claim.terms.values_mut() {
                *coefficient *= 2;
            }
            claim.constant *= 2;
            nodes.push(IntegerArithmeticNode::Add {
                left: source,
                right: source,
                result: claim.clone(),
            });
        }
        let factor = BigInt::one() << depth;
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                IntegerTerm::multiply(IntegerTerm::Constant(factor.clone()), x.as_ref().clone())
                    .into(),
                IntegerTerm::multiply(IntegerTerm::Constant(factor.clone()), y.as_ref().clone())
                    .into(),
            ),
            true,
        );
        let surface_goal = compare(
            multiply(literal(&factor), ContractExpression::Binding("x".into())),
            false,
            multiply(literal(&factor), ContractExpression::Binding("y".into())),
        );
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let file = crate::surface::parse("").unwrap();
        let definitions = proof_theorem_definitions(&file).unwrap();
        let theorems = TheoremEnvironment::new(&definitions);
        let root = Proof::for_pure_surface_goal(
            "composition sharing",
            &context.requires,
            goal,
            surface_goal.clone(),
            &context,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let plan = IntegerArithmeticCertificate {
            nodes,
            conclusion: depth,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::apply_integer_composition(
                &root,
                &plan,
                &[(premise, surface)],
                &surface_goal,
                &[],
            )
        });
        let result = result
            .unwrap_or_else(|error| panic!("{}", error.message()))
            .expect("the shared plan is supported");
        assert!(result.is_complete());
        let certificate = result.certificate();
        let printed = format!("{:?}", certificate.steps());
        assert!(!printed.contains("Normalize"), "{printed}");
        (work, printed.len(), certificate.steps().len())
    }

    #[test]
    #[ignore = "nightly: shared-plan construction takes 0.6s in parallel"]
    fn integer_composition_shared_plan_constructs_each_node_once() {
        let (_, _, steps) = shared_plan(2, 0, false);
        assert!(
            steps <= 2 + 8,
            "shared derivations became nested proof copies: {steps}"
        );
    }

    macro_rules! composition_case {
        ($(#[$meta:meta])* $name:ident, $parameters:literal, $requirements:literal, $goal:literal) => {
            #[test]
            $(#[$meta])*
            fn $name() {
                let source = format!(
                    "theorem composition({}) {{ {} ensures {} by {{ solve() using {{ {} }}; }} }}",
                    $parameters,
                    $requirements,
                    $goal,
                    $requirements.replace("requires ", "")
                );
                let expanded =
                    expand_c_claim_source_by_label(&source, &[], "composition.ensures_0")
                        .unwrap_or_else(|error| panic!("{}", error.message()));
                assert!(
                    !expanded.contains("normalize("),
                    "{expanded}\nComposition refusal: {:?}",
                    super::LAST_FAILURE.with(|failure| failure.borrow_mut().take())
                );
                assert!(!expanded.contains("solve("), "{expanded}");
                without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                    .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
            }
        };
    }
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_premise,
        "x: Integer, y: Integer",
        "requires x < y;",
        "2 * x + 2 <= 2 * y"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_goal,
        "x: Integer, y: Integer",
        "requires x + 1 <= y;",
        "x < y"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_negative_premise,
        "x: Integer",
        "requires not (x <= 3);",
        "4 <= x"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_strict_disequality,
        "x: Integer, y: Integer",
        "requires x <= y; requires x != y;",
        "x < y"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_refutation_chain,
        "a: Integer, b: Integer, c: Integer, d: Integer, e: Integer",
        "requires a <= b; requires b <= c; requires c <= d; requires d <= e;",
        "a <= e"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_rounding,
        "x: Integer",
        "requires 2 * x <= 5;",
        "x <= 2"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_native_bridge,
        "x: uint64",
        "requires x <= 5u64;",
        "2 * to_integer(x) <= 10"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_intrinsic_range,
        "x: int64",
        "",
        "-9223372036854775808 <= to_integer(x)"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_intrinsic_quotient,
        "x: uint64",
        "",
        "4 * to_integer(x / 4u64) <= to_integer(x)"
    );
    composition_case!(
        #[ignore = "nightly: complete arithmetic migration expansion and replay"]
        integer_migration_excluded_endpoint,
        "x: uint64",
        "requires x != 0u64;",
        "0u64 < x"
    );
    composition_case!(
        #[ignore = "nightly: minimal scaled-bound expansion and replay took 2.1s in parallel"]
        integer_composition_single_scaled_bound,
        "x: Integer",
        "requires x <= 3;",
        "2 * x <= 6"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6s in parallel"]
        integer_composition_scaled_sum,
        "x: Integer, y: Integer",
        "requires x <= 3; requires y <= 4;",
        "2 * x + 3 * y <= 18"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_three_bounds,
        "x: Integer, y: Integer, z: Integer",
        "requires x <= 3; requires y <= 4; requires z <= 5;",
        "2 * x + 3 * y + z <= 23"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_equality_direction,
        "x: Integer, y: Integer",
        "requires x == y + 1; requires y <= 5;",
        "x <= 6"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_antisymmetry,
        "x: Integer, y: Integer",
        "requires x <= y; requires y <= x;",
        "x == y"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_negative_equality_scale,
        "x: Integer, y: Integer",
        "requires x == y + 1;",
        "-2 * x + 2 * y == -2"
    );
    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
        integer_composition_equality_sum,
        "x: Integer, y: Integer",
        "requires x == 2; requires y == 3;",
        "x + y == 5"
    );

    composition_case!(
        #[ignore = "nightly: ordinary expansion and replay"]
        integer_composition_greater_equal_spelling,
        "x: Integer",
        "requires x >= 3;",
        "2 * x >= 6"
    );

    #[test]
    #[ignore = "nightly: wide default expansion and replay"]
    fn integer_composition_wide_constant_keeps_integer_context_after_expansion() {
        let source = "theorem composition(z: Integer) { requires 0 <= z; requires z <= 4000; ensures z <= 18446744073709551615 by { solve(); } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("normalize("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[ignore = "nightly: two composed branches and replay"]
    fn integer_composition_closes_its_focused_conjunction_branch() {
        let source = "theorem composition(x: Integer) { requires x <= 3; ensures 2 * x <= 6 and 3 * x <= 9 by { both { solve() using { x <= 3; }; } and { solve() using { x <= 3; }; } } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("normalize("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
    fn integer_composition_unrestricted_solve_uses_the_same_ordinary_emitter() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { solve(); } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
    fn integer_composition_preserves_original_alias_and_nonlinear_operand_spellings() {
        for source in [
            "theorem composition(x: Integer, y: Integer) { let z: Integer = x + y; requires z <= 3; ensures 2 * z <= 6 by { solve() using { z <= 3; }; } }",
            "theorem composition(x: Integer, y: Integer) { requires x * y <= 3; ensures 2 * (x * y) <= 6 by { solve() using { x * y <= 3; }; } }",
        ] {
            let expanded =
                expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
            assert!(!expanded.contains("normalize("), "{expanded}");
            without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        }
    }

    #[test]
    fn integer_composition_does_not_use_an_unlisted_bound() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { solve() using { x <= 3; }; } }";
        assert!(verify_c_sources(source, &[]).is_err());
    }

    #[test]
    #[ignore = "nightly: identity expansion, replay and known refusal take 0.5s"]
    fn integer_identity_solve_expands_to_explicit_arithmetic_without_normalize() {
        let source = "theorem identity(x: Integer, y: Integer) { ensures 3 * (x - y) == x + x + x - 3 * y by { solve(); } }";
        let expanded = expand_c_claim_source_by_label(source, &[], "identity.ensures_0").unwrap();
        assert!(expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        assert!(verify_c_sources(&source.replace("solve();", "known();"), &[]).is_err());
    }

    #[test]
    #[ignore = "nightly: selected expansion, replay and missing-premise control take 0.8s"]
    fn integer_composition_selected_bounds_expand_without_normalize() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { solve() using { x <= 3; y <= 4; }; } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(expanded.contains("arithmetic_certificate"), "{expanded}");
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        assert!(verify_c_sources(&source.replace("x <= 3; y <= 4;", "x <= 3;"), &[]).is_err());
    }

    #[test]
    fn explicit_integer_scaling_normalization_keeps_known_and_multi_step_expansion_opaque() {
        let source = "theorem identity(x: Integer, y: Integer) { ensures 3 * (x - y) == x + x + x - 3 * y by { normalize(); } }";
        without_implicit_solve(|| verify_c_sources(source, &[])).unwrap();
        assert!(verify_c_sources(&source.replace("normalize();", "known();"), &[]).is_err());
        for source in [
            "theorem nonlinear(x: Integer, y: Integer, z: Integer, w: Integer) { ensures (x + y) * (z + w) == x * z + x * w + y * z + y * w by { normalize(); } }",
            "theorem wrong(x: Integer) { ensures 2 * x == x + x + 1 by { normalize(); } }",
            "theorem ignores_facts(x: Integer) { requires x == 0; ensures 2 * x == 3 * x by { normalize(); } }",
        ] {
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::tests::*;
    include!("../../../scaling_tests/surface/proof/smart_closures/integer_composition/tests.rs");
}
