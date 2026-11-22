use super::*;

#[test]
fn addressed_result_members_bind_the_builtin_and_preserve_explicit_program_names() {
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, mut context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        ProgramValueBindings::new(),
        ProgramValueBindings::new(),
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    context.contract_result_in_scope = true;
    let member = |name: &str| {
        crate::kernel::program_expression::typed_load(
            ProgramExpression::Subobject {
                pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                    pointer: Box::new(ProgramExpression::Variable(name.into())),
                    bytes: 8.into(),
                }),
                width: 4,
            },
            ProgramType::Int32,
        )
    };
    for (base, expected, in_scope, operand_name) in [
        (
            ContractExpression::ProgramExpression(ProgramExpression::Variable("result".into())),
            crate::kernel::CONTRACT_RESULT,
            true,
            "result",
        ),
        (
            ContractExpression::ProgramBinding("result".into()),
            crate::kernel::BindingName::from("result"),
            true,
            "result",
        ),
        (
            ContractExpression::ProgramExpression(ProgramExpression::Variable("bound".into())),
            crate::kernel::BindingName::from("bound"),
            false,
            "bound",
        ),
    ] {
        context.contract_result_in_scope = in_scope;
        let place = member(operand_name);
        let expression = ContractExpression::CUnary {
            operand: Box::new(ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(base),
                field: "value".into(),
                lowered: place.clone(),
                offset_bytes: 8.into(),
            }),
            lowered: ProgramExpression::AddressOf(Box::new(member("result"))),
        };
        let lowered = lowerer
            .lower_contract_expression_to_spec(&expression, &context)
            .expect("the selected member address lowers in the result scope");
        assert_eq!(
            lowered,
            SpecExpression::ObjectAddress(Box::new(crate::kernel::SpecObjectAddress {
                base: Box::new(SpecExpression::ProgramExpression(
                    ProgramExpression::Variable(expected)
                )),
                steps: vec![
                    crate::kernel::SpecAddressStep::Subobject { width: 4 },
                    crate::kernel::SpecAddressStep::OffsetBytes { bytes: 8.into() }
                ],
                value_type: ProgramType::Int32,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
                checked: false,
            })),
        );
    }
}

#[test]
fn struct_pointer_arithmetic_through_uint64_cast_uses_layout_width() {
    let function = crate::languages::c::syntax::parse_function(
        r#"
            struct pair {
                int32 a;
                int64 b;
            };
            int32 f(struct pair* p, int32 i) { return 0; }
        "#,
    )
    .expect("struct pointer function should parse");
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        ProgramValueBindings::new(),
        ProgramValueBindings::new(),
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        parameter_pointer_element_widths(function.parameters()),
    );
    let pointer_add = ProgramExpression::Add(
        Box::new(ProgramExpression::Variable("p".into())),
        Box::new(ProgramExpression::Variable("i".into())),
    );
    let cast = ProgramExpression::Cast {
        expression: Box::new(pointer_add),
        target_type: ProgramType::UInt64,
        integer_mode: crate::kernel::IntegerCastMode::Standard,
        pointee_struct: None,
        pointee_struct_size: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let lowered = lowerer
        .lower_program_expression_to_spec(&cast, &context)
        .expect("pointer arithmetic should lower");
    let SpecExpression::Cast(pointer, ProgramType::UInt64) = lowered else {
        panic!("expected a preserved uint64 cast around pointer arithmetic");
    };
    let SpecExpression::PointerOffset { byte_width, .. } = pointer.as_ref() else {
        panic!("expected pointer arithmetic to lower as a pointer offset");
    };
    assert_eq!(*byte_width, 16);
}

#[test]
fn integer_binder_contexts_share_unrelated_machine_bindings() {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let mut all_costs = Vec::new();
    for unrelated in [0, 64, 256, 1024] {
        let context = SpecElaborationContext {
            values: (0..unrelated)
                .map(|index| {
                    (
                        format!("unrelated{index}"),
                        SpecExpression::Value(ProgramValue::Int32(MachineTerm::Variable(
                            Variable(index),
                        ))),
                    )
                })
                .collect(),
            ..SpecElaborationContext::default()
        };
        let mut costs = Vec::new();
        for depth in [8, 16, 32, 64] {
            let before = crate::persistent::persistent_node_allocations();
            let mut scope = context.clone();
            assert_eq!(crate::persistent::persistent_node_allocations(), before);
            for index in 0..depth {
                let mut child = scope.clone();
                child.integer_values.insert(
                    format!("bound{index}"),
                    SpecIntegerExpression::Term(IntegerTerm::var(Variable(index + 2000))),
                );
                assert!(child.values.shares_root_with(&context.values));
                assert!(
                    child
                        .algebraic_values
                        .shares_root_with(&context.algebraic_values)
                );
                assert!(child.array_refs.shares_root_with(&context.array_refs));
                scope = child;
            }
            assert_eq!(context.integer_values.len(), 0);
            assert_eq!(scope.integer_values.len(), depth as usize);
            costs.push(crate::persistent::persistent_node_allocations() - before);
        }
        for pair in costs.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "{costs:?}");
        }
        all_costs.push(costs);
    }
    assert!(
        all_costs.windows(2).all(|pair| pair[0] == pair[1]),
        "{all_costs:?}"
    );
}

thread_local! {
    pub(super) static PROPOSITION_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[test]
fn nested_state_propositions_lower_with_small_frames_and_linear_visits() {
    std::thread::Builder::new()
        .name("small-stack-proposition-lowering".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = ExecutionState::new().with_local("x", int32(7));
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let mut retained_states = RecordedStates::default();
            retained_states.insert(ProgramPointSelector::Mark("before".into()), state.clone());
            let atom = || ClickProposition::Comparison {
                left: ContractExpression::At {
                    selector: ProgramPointSelector::Mark("before".into()),
                    expression: Box::new(ContractExpression::ProgramExpression(
                        ProgramExpression::Variable("x".into()),
                    )),
                },
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(7))),
            };
            for depth in [4, 8, 16, 32] {
                let mut proposition = atom();
                for level in 0..depth {
                    let left = Box::new(atom());
                    let right = Box::new(proposition);
                    proposition = match level % 3 {
                        0 => ClickProposition::And(left, right),
                        1 => ClickProposition::Or(left, right),
                        _ => ClickProposition::Implies(left, right),
                    };
                }
                let (mut lowerer, context) = fixed_state_elaboration(
                    BTreeMap::new(),
                    BTreeMap::new(),
                    &state,
                    ProgramValueBindings::from([("x".into(), int32(7))]),
                    ProgramValueBindings::from([("x".into(), int32(9))]),
                    None,
                    &retained_states,
                    SpecDefinitions::new(&predicates, &functions),
                    BTreeSet::new(),
                    BTreeMap::new(),
                );
                PROPOSITION_VISITS.with(|visits| visits.set(0));
                let lowered = lowerer
                    .click_proposition_to_spec_proposition(&proposition, &context)
                    .unwrap();
                assert_eq!(
                    PROPOSITION_VISITS.with(|visits| visits.get()),
                    2 * depth + 1
                );
                let mut pending = vec![&lowered];
                let mut leaves = 0;
                while let Some(node) = pending.pop() {
                    match node {
                        SpecProposition::And(left, right)
                        | SpecProposition::Or(left, right)
                        | SpecProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        SpecProposition::Comparison { left, right, .. } => {
                            assert!(
                                matches!(left, SpecExpression::Value(value) if value == &int32(7))
                            );
                            assert!(
                                matches!(right, SpecExpression::Value(value) if value == &int32(7))
                            );
                            leaves += 1;
                        }
                        _ => panic!("lowering changed the proposition shape"),
                    }
                }
                assert_eq!(leaves, depth + 1);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A `decreases` component is refused when it names a state of its own,
/// wherever inside the component that state is named. The kernel reads the one
/// declared component at two states and ranks the values; a component that
/// fixes its own state reads one state twice, so both `old(...)` and any
/// `at(...)` state, including a loop's own entry, are refused.
#[test]
fn a_fixed_state_anywhere_in_a_measure_is_found() {
    let current = ContractExpression::ProgramBinding("n".to_string());
    assert!(fixed_measure_state(&current).is_none());

    let old = ContractExpression::Subtract(
        Box::new(current.clone()),
        Box::new(ContractExpression::Old(Box::new(current.clone()))),
    );
    assert!(matches!(
        fixed_measure_state(&old),
        Some(FixedMeasureState::Old)
    ));

    let loop_entry = ProgramPointSelector::ProgramPoint(ProgramPointRef {
        region: CodeRegionRef::Loop(0),
        kind: ProgramPointKind::Entry,
    });
    let at = ContractExpression::Call {
        name: "head".to_string(),
        arguments: vec![ContractExpression::At {
            selector: loop_entry.clone(),
            expression: Box::new(current),
        }],
    };
    let found = fixed_measure_state(&at).expect("a state in a call argument is a state");
    let FixedMeasureState::At(selector) = &found else {
        panic!("the refusal names the state, not `old`");
    };
    assert_eq!(selector, &loop_entry);
    assert_eq!(found.spelling(), "at(loop(0).entry, ...)");
}

#[test]
fn surface_binder_streams_are_their_own_producers() {
    use crate::kernel::Producer;
    let mut next = 7;
    let variable = allocate_quantifier_variable(&mut next, Producer::ProofQuantifier).unwrap();
    assert_eq!(variable, Variable::produced(Producer::ProofQuantifier, 7));
    assert_eq!(next, 8);
    assert_ne!(variable, Variable(7));
    assert_ne!(
        variable,
        Variable::produced(Producer::FunctionQuantifier, 7)
    );
    let mut last = u64::MAX;
    assert!(allocate_quantifier_variable(&mut last, Producer::ProofQuantifier).is_err());

    // Algebraic binders have their own origin, so no index reaches another
    // producer's identities.
    let binder = algebraic_binder_variable(usize::MAX).unwrap();
    assert_eq!(binder.algebraic_binder_index(), Some(usize::MAX as u64));
    assert_ne!(binder, Variable(binder.0));
}

#[test]
fn captured_identities_of_other_producers_do_not_move_the_quantifier_stream() {
    use crate::kernel::Producer;
    let own = Variable::produced(Producer::ProofQuantifier, 12);
    let other = Variable::produced(Producer::FunctionQuantifier, 40);
    let ordinary = Variable((1 << 43) + 17);
    let term = |variable| {
        Box::new(crate::kernel::SpecIntegerExpression::Term(
            crate::kernel::IntegerTerm::var(variable),
        ))
    };
    let captured = crate::kernel::SpecIntegerExpression::Add(
        term(own),
        Box::new(crate::kernel::SpecIntegerExpression::Add(
            term(other),
            term(ordinary),
        )),
    );
    assert_eq!(
        max_spec_integer_expression_variable(&captured, Producer::ProofQuantifier),
        Some(own)
    );
    assert_eq!(
        max_spec_integer_expression_variable(&captured, Producer::ResourceQuantifier),
        None
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/lowering/annotations/tests.rs");
}

/// One walk's loop index agrees with the per-index walk it replaces at every
/// index, across nested, `for`, `do` and `if`-arm loops, and past the end.
#[test]
fn c_loop_index_agrees_with_the_walk_at_every_loop() {
    let function = crate::languages::c::syntax::parse_function(
        r#"
            int32 f(int32 n) {
                int32 i;
                int32 j;
                i = 0;
                while (i < n) {
                    j = 0;
                    while (j < n) { j = j + 1; }
                    i = i + 1;
                }
                for (i = 0; i < n; i = i + 1) {
                    j = 0;
                    do { j = j + 1; } while (j < n);
                }
                if (n > 0) {
                    while (i > 0) { i = i - 1; }
                } else {
                    do { i = i + 1; } while (i < 2);
                }
                return 0;
            }
        "#,
    )
    .expect("loop function should parse");
    let index = c_loops_by_index(function.body());
    assert_eq!(index.len(), 6);
    for target in 0..index.len() + 2 {
        assert_eq!(
            index.get(target).and_then(Option::as_ref),
            c_loop_by_index(function.body(), target),
            "loop({target})"
        );
    }
}

#[test]
fn ordinary_integer_arithmetic_retains_structure_and_deferred_domain_checks() {
    use crate::kernel::{IntegerTerm as Int, SpecIntegerExpression as Spec};
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, mut context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        ProgramValueBindings::new(),
        ProgramValueBindings::new(),
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    let x = Int::Variable(crate::kernel::Variable(914002));
    context.integer_values = context
        .integer_values
        .with_inserted("x", Spec::Term(x.clone()));
    let binding = || Box::new(ContractExpression::Binding("x".into()));
    let one = || Box::new(ContractExpression::IntegerLiteral("1".into()));
    for (expression, expected) in [
        (
            ContractExpression::Negate(binding()),
            Int::Negate(x.clone().into()),
        ),
        (
            ContractExpression::Add(binding(), one()),
            Int::Add(x.clone().into(), Int::constant_i64(1).into()),
        ),
        (
            ContractExpression::Subtract(binding(), binding()),
            Int::Subtract(x.clone().into(), x.clone().into()),
        ),
        (
            ContractExpression::Multiply(binding(), one()),
            Int::Multiply(x.clone().into(), Int::constant_i64(1).into()),
        ),
    ] {
        assert_eq!(
            lowerer
                .lower_contract_integer_to_spec(&expression, &context)
                .unwrap(),
            Spec::Term(expected)
        );
    }
    for name in ["truncating_quotient", "truncating_remainder"] {
        let call = |divisor| ContractExpression::Call {
            name: name.into(),
            arguments: vec![*binding(), divisor],
        };
        let pure = lowerer
            .lower_contract_integer_to_spec(&call(*one()), &context)
            .unwrap();
        assert_eq!(
            pure,
            Spec::Term(if name == "truncating_quotient" {
                Int::TruncatingQuotient(x.clone().into(), Int::constant_i64(1).into())
            } else {
                Int::TruncatingRemainder(x.clone().into(), Int::constant_i64(1).into())
            })
        );
        // A symbolic divisor still needs its ordinary nonzero obligation.
        let deferred = lowerer
            .lower_contract_integer_to_spec(&call(*binding()), &context)
            .unwrap();
        assert!(matches!(
            deferred,
            Spec::TruncatingQuotient(..) | Spec::TruncatingRemainder(..)
        ));
    }
}

#[test]
fn fixed_contract_result_is_separate_from_lexical_result_in_old_states() {
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let result = int32(11);
    let (mut lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        ProgramValueBindings::from([("result".into(), int32(3))]),
        ProgramValueBindings::from([("result".into(), int32(7))]),
        Some(&result),
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    let old_context = context
        .old_state(&lowerer.entry_values, &state.program_point())
        .unwrap();
    for (context, lexical) in [(&context, 7), (&old_context, 3)] {
        for expression in [
            ContractExpression::Binding("result".into()),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::CONTRACT_RESULT,
            )),
        ] {
            assert_eq!(
                lowerer
                    .lower_contract_expression_to_spec(&expression, context)
                    .unwrap(),
                SpecExpression::Value(result.clone())
            );
        }
        assert_eq!(
            lowerer
                .lower_contract_expression_to_spec(
                    &ContractExpression::ProgramBinding("result".into()),
                    context
                )
                .unwrap(),
            SpecExpression::Value(int32(lexical))
        );
    }
}

#[test]
fn common_integer_comparisons_keep_operands_and_native_fact_shape() {
    use crate::kernel::{ConditionTerm, IntegerTerm, KernelTermNode, SpecIntegerExpression};
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(999995);
    let bindings = PersistentBinderMap::default().with_inserted(
        "x",
        SpecIntegerExpression::Term(IntegerTerm::Variable(variable)),
    );
    let left = SurfaceTerm::Add(
        Box::new(SurfaceTerm::Binding("x".into())),
        Box::new(SurfaceTerm::IntegerLiteral("1".into())),
    );
    let right = SurfaceTerm::Binding("x".into());
    let a: crate::kernel::SharedIntegerTerm = IntegerTerm::Add(
        IntegerTerm::Variable(variable).into(),
        IntegerTerm::constant_i64(1).into(),
    )
    .into();
    let b: crate::kernel::SharedIntegerTerm = IntegerTerm::Variable(variable).into();
    for (operator, expected) in [
        (
            ComparisonOperator::Equal,
            ConditionTerm::IntegerEqual(a.clone(), b.clone()),
        ),
        (
            ComparisonOperator::NotEqual,
            ConditionTerm::IntegerNotEqual(a.clone(), b.clone()),
        ),
        (
            ComparisonOperator::LessThan,
            ConditionTerm::IntegerLessThan(a.clone(), b.clone()),
        ),
        (
            ComparisonOperator::LessEqual,
            ConditionTerm::IntegerLessEqual(a.clone(), b.clone()),
        ),
        (
            ComparisonOperator::GreaterThan,
            ConditionTerm::IntegerGreaterThan(a.clone(), b.clone()),
        ),
        (
            ComparisonOperator::GreaterEqual,
            ConditionTerm::IntegerGreaterEqual(a.clone(), b.clone()),
        ),
    ] {
        let root = lower_surface_integer_comparison(&left, operator, &right, &bindings).unwrap();
        let KernelTermNode::IntegerCompare { arguments, .. } = root.node() else {
            panic!()
        };
        assert!(matches!(
            arguments[0].node(),
            KernelTermNode::IntegerOperation { .. }
        ));
        assert!(matches!(arguments[1].node(), KernelTermNode::Variable(v) if *v == variable));
        let source = ClickProposition::Comparison {
            left: left.clone(),
            operator,
            right: right.clone(),
        };
        assert_eq!(
            lower_integer_arithmetic_proposition(&source, &bindings).unwrap(),
            Proposition::condition_is(expected, true)
        );
    }
}

/// `exact(place)` lowers the place as an ordinary read and names only its
/// outermost read by the state in scope (`design/exact-reads.md`): the
/// reads that compute the place's address stay ordinary, and wrapping an
/// inner read makes that read exact too. A place that is not a memory read
/// is refused rather than read as itself.
#[test]
fn an_exact_read_marks_only_its_outermost_read() {
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let pp = ProgramValue::typed_pointer(
        Address::symbolic(Variable(914_101)),
        ProgramType::Int32PointerPointer,
    );
    let bindings = ProgramValueBindings::from([("pp".into(), pp.clone()), ("x".into(), int32(4))]);
    let (mut lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        bindings.clone(),
        bindings,
        None,
        &retained_states,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    let zero = || Box::new(ProgramExpression::Value(int32(0)));
    // `pp[0]` and `pp[0][0]`, as C places.
    let inner =
        ProgramExpression::Index(Box::new(ProgramExpression::Variable("pp".into())), zero());
    let outer = ProgramExpression::Index(Box::new(inner.clone()), zero());
    let place = |expression: &ProgramExpression| {
        Box::new(ContractExpression::ProgramExpression(expression.clone()))
    };
    let mut lower = |expression: ContractExpression| {
        lowerer.lower_contract_expression_to_spec(&expression, &context)
    };
    // Returns the read's `exact` flag and, for a read through a pointer read,
    // that inner read's flag.
    fn flags(read: &SpecExpression) -> (bool, Option<bool>) {
        let SpecExpression::MemoryLoad { pointer, exact, .. } = read else {
            panic!("a memory read: {read:?}")
        };
        let inner = match pointer.as_ref() {
            SpecExpression::PointerOffset { pointer, .. } => match pointer.as_ref() {
                SpecExpression::MemoryLoad { exact, .. } => Some(*exact),
                _ => None,
            },
            _ => None,
        };
        (*exact, inner)
    }
    let ordinary = lower(*place(&inner)).unwrap();
    let exact = lower(ContractExpression::Exact(place(&inner))).unwrap();
    assert_eq!(flags(&ordinary), (false, None));
    assert_eq!(flags(&exact), (true, None));
    // Apart from naming, the exact read is the ordinary one.
    let unmarked = match exact.clone() {
        SpecExpression::MemoryLoad {
            point,
            pointer,
            value_type,
            ..
        } => SpecExpression::MemoryLoad {
            point,
            pointer,
            value_type,
            exact: false,
        },
        _ => unreachable!(),
    };
    assert_eq!(unmarked, ordinary);

    // `exact(pp[0][0])`: the address read `pp[0]` stays ordinary.
    let outermost = lower(ContractExpression::Exact(place(&outer))).unwrap();
    assert_eq!(flags(&outermost), (true, Some(false)));
    assert_eq!(flags(&lower(*place(&outer)).unwrap()), (false, Some(false)));
    // `exact(exact(pp[0])[0])` makes both reads exact.
    let both = lower(ContractExpression::Exact(Box::new(
        ContractExpression::Index(
            Box::new(ContractExpression::Exact(place(&inner))),
            Box::new(ContractExpression::IntegerLiteral("0".into())),
        ),
    )))
    .unwrap();
    assert_eq!(flags(&both), (true, Some(true)));

    // A parameter's value is not a memory read.
    let refused = lower(ContractExpression::Exact(Box::new(
        ContractExpression::Binding("x".into()),
    )))
    .unwrap_err();
    assert!(
        refused.contains("`exact` takes a memory read, such as `p[i]` or `h->next`"),
        "{refused}"
    );
}
