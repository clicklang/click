//! Ordinary proofs of the composition fragment of Integer arithmetic plans.
//! Node results use flat linear forms over the original source operands. A
//! node never embeds another node's source tree, even when the plan is a DAG.
use super::*;
use crate::kernel::SharedIntegerTerm;

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
}

fn literal(value: &BigInt) -> ContractExpression {
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
fn normalization(claim: ClickProposition) -> ProofStep {
    have(claim, vec![ProofStep::Normalize])
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

/// Restate one relation by explicitly proved identities of its operands.
/// There is no affine reasoning over facts hidden in `normalize using`:
/// all the algebra is in the two context-free identity goals.
fn transfer(target: &ClickProposition, fact: &ClickProposition) -> Vec<ProofStep> {
    let (a, operator, b) = integer_surface_ordered_parts(target).expect("composition target");
    let (c, _, d) = integer_surface_ordered_parts(fact).expect("composition fact");
    let left = compare(a.clone(), true, c.clone());
    let right = compare(b.clone(), true, d.clone());
    vec![
        normalization(left.clone()),
        normalization(right.clone()),
        application(
            if operator == ComparisonOperator::Equal {
                "equal_substitute"
            } else {
                "le_substitute"
            },
            vec![c, d, a, b],
            vec![fact.clone(), left, right],
        ),
    ]
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

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn apply_integer_composition(
        proof: &Proof<'a>,
        plan: &IntegerArithmeticCertificate,
        pairs: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_integer_composition");
        let Some(goal) = proof.goal() else {
            return Ok(None);
        };
        let Some((_, goal_equal, _)) = parts(goal) else {
            return Ok(None);
        };
        let Some((goal_left, goal_operator, goal_right)) =
            integer_surface_ordered_parts(surface_goal)
        else {
            return Ok(None);
        };
        if !matches!(
            goal_operator,
            ComparisonOperator::Equal | ComparisonOperator::LessEqual
        ) {
            return Ok(None);
        }
        let Some(expected) = integer_affine_claim(goal) else {
            return Ok(None);
        };
        let mut used = BTreeSet::new();
        let mut pending = vec![plan.conclusion];
        while let Some(index) = pending.pop() {
            if !used.insert(index) {
                continue;
            }
            let Some(node) = plan.nodes.get(index) else {
                return Ok(None);
            };
            let result = match node {
                IntegerArithmeticNode::Premise { index, result } => {
                    let Some((kernel, surface)) = pairs.get(*index) else {
                        return Ok(None);
                    };
                    if parts(kernel).is_none()
                        || !matches!(
                            integer_surface_ordered_parts(surface),
                            Some((
                                _,
                                ComparisonOperator::Equal | ComparisonOperator::LessEqual,
                                _
                            ))
                        )
                    {
                        return Ok(None);
                    }
                    result
                }
                IntegerArithmeticNode::Scale { source, result, .. }
                | IntegerArithmeticNode::EqualityToLessEqual { source, result, .. } => {
                    pending.push(*source);
                    result
                }
                IntegerArithmeticNode::Add {
                    left,
                    right,
                    result,
                } => {
                    pending.extend([*left, *right]);
                    result
                }
                IntegerArithmeticNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => {
                    pending.extend([*lower, *upper]);
                    result
                }
                IntegerArithmeticNode::Trivial { result } => result,
                _ => return Ok(None),
            };
            if index == plan.conclusion && result != &expected {
                return Ok(None);
            }
        }
        let mut atoms = BTreeMap::new();
        let mut nodes: BTreeMap<usize, Node> = BTreeMap::new();
        let mut steps = Vec::new();
        let ordered_goal = compare(goal_left, goal_equal, goal_right.clone());
        for index in used {
            check_verification_deadline()?;
            let (form, equal, body) = match &plan.nodes[index] {
                IntegerArithmeticNode::Premise { index, .. } => {
                    let (kernel, surface) = &pairs[*index];
                    let (a, equal, b) = parts(kernel).expect("supported premise");
                    let (left, _, right) =
                        integer_surface_ordered_parts(surface).expect("supported source");
                    let form = operand(a, left.clone(), &mut atoms)
                        .add(&operand(b, right.clone(), &mut atoms).scaled(&BigInt::from(-1)));
                    let target = compare(expression(&form, &atoms), equal, zero());
                    let ordered = compare(left.clone(), equal, right.clone());
                    let mut body = Vec::new();
                    if &ordered != surface {
                        body.push(have(
                            ordered.clone(),
                            vec![ProofStep::NormalizeUsing(vec![surface.clone()])],
                        ));
                    }
                    let shifted = if equal {
                        let fact = compare(
                            ContractExpression::Subtract(
                                Box::new(left.clone()),
                                Box::new(right.clone()),
                            ),
                            true,
                            zero(),
                        );
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "equal_difference",
                                vec![left, right],
                                vec![ordered],
                            )],
                        ));
                        fact
                    } else {
                        let negative = ContractExpression::Negate(Box::new(right.clone()));
                        let reflexive = compare(negative.clone(), false, negative.clone());
                        body.push(normalization(reflexive.clone()));
                        let fact = compare(
                            add(left.clone(), negative.clone()),
                            false,
                            add(right.clone(), negative.clone()),
                        );
                        body.push(have(
                            fact.clone(),
                            vec![application(
                                "add_le",
                                vec![left, right, negative.clone(), negative],
                                vec![ordered, reflexive],
                            )],
                        ));
                        fact
                    };
                    body.extend(transfer(&target, &shifted));
                    (form, equal, body)
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
                        body.push(normalization(positive.clone()));
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
                        normalization(reflexive.clone()),
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
                    vec![ProofStep::Normalize],
                ),
                _ => unreachable!("unsupported rules are excluded before constructing any proof"),
            };
            let claim = compare(expression(&form, &atoms), equal, zero());
            steps.push(have(claim.clone(), body));
            nodes.insert(index, Node { form, equal, claim });
        }
        let conclusion = &nodes[&plan.conclusion];
        let value = expression(&conclusion.form, &atoms);
        if goal_equal {
            let reflexive = compare(goal_right.clone(), true, goal_right.clone());
            let fact = compare(
                add(value.clone(), goal_right.clone()),
                true,
                add(zero(), goal_right.clone()),
            );
            steps.push(normalization(reflexive.clone()));
            steps.push(have(
                fact.clone(),
                vec![application(
                    "equal_add",
                    vec![value, zero(), goal_right.clone(), goal_right.clone()],
                    vec![conclusion.claim.clone(), reflexive],
                )],
            ));
            steps.extend(transfer(&ordered_goal, &fact));
        } else {
            let reflexive = compare(goal_right.clone(), false, goal_right.clone());
            let fact = compare(
                add(value.clone(), goal_right.clone()),
                false,
                add(zero(), goal_right.clone()),
            );
            steps.push(normalization(reflexive.clone()));
            steps.push(have(
                fact.clone(),
                vec![application(
                    "add_le",
                    vec![value, zero(), goal_right.clone(), goal_right],
                    vec![conclusion.claim.clone(), reflexive],
                )],
            ));
            steps.extend(transfer(&ordered_goal, &fact));
        }
        if &ordered_goal != surface_goal {
            steps = vec![
                have(ordered_goal.clone(), steps),
                ProofStep::NormalizeUsing(vec![ordered_goal]),
            ];
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
                    .with(|failure| *failure.borrow_mut() = Some(error.message().to_owned()));
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
            )
        });
        let result = result
            .unwrap_or_else(|error| panic!("{}", error.message()))
            .expect("the shared plan is supported");
        assert!(result.is_complete());
        let certificate = result.certificate();
        let printed = format!("{:?}", certificate.steps());
        assert!(!printed.contains("ArithmeticCertificate"));
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
                    !expanded.contains("arithmetic_certificate"),
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
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[ignore = "nightly: two composed branches and replay"]
    fn integer_composition_closes_its_focused_conjunction_branch() {
        let source = "theorem composition(x: Integer) { requires x <= 3; ensures 2 * x <= 6 and 3 * x <= 9 by { both { solve() using { x <= 3; }; } and { solve() using { x <= 3; }; } } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
    }

    #[test]
    #[ignore = "nightly: ordinary expansion and replay take 0.6–0.8s in parallel"]
    fn integer_composition_unrestricted_solve_uses_the_same_ordinary_emitter() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { solve(); } }";
        let expanded =
            expand_c_claim_source_by_label(source, &[], "composition.ensures_0").unwrap();
        assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
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
            assert!(!expanded.contains("arithmetic_certificate"), "{expanded}");
            without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        }
    }

    #[test]
    fn integer_composition_does_not_use_an_unlisted_bound() {
        let source = "theorem composition(x: Integer, y: Integer) { requires x <= 3; requires y <= 4; ensures 2 * x + 3 * y <= 18 by { solve() using { x <= 3; }; } }";
        assert!(verify_c_sources(source, &[]).is_err());
    }

    #[test]
    fn explicit_integer_scaling_normalization_keeps_known_and_nonlinear_products_opaque() {
        let source = "theorem identity(x: Integer, y: Integer) { ensures 3 * (x - y) == x + x + x - 3 * y by { normalize(); } }";
        without_implicit_solve(|| verify_c_sources(source, &[])).unwrap();
        assert!(verify_c_sources(&source.replace("normalize();", "known();"), &[]).is_err());
        for source in [
            "theorem nonlinear(x: Integer, y: Integer, z: Integer) { ensures (x + y) * z == x * z + y * z by { normalize(); } }",
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
