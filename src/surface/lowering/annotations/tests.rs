use super::*;

#[test]
fn addressed_result_members_bind_the_builtin_and_preserve_explicit_c_names() {
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (mut lowerer, mut context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        BTreeMap::new(),
    );
    context.contract_result_in_scope = true;
    let member = |name: &str| {
        crate::kernel::c_typed_load(
            CExpression::Subobject {
                pointer: Box::new(CExpression::PointerOffsetBytes {
                    pointer: Box::new(CExpression::Variable(name.into())),
                    bytes: 8,
                }),
                width: 4,
            },
            CType::Int32,
        )
    };
    for (base, expected, in_scope, operand_name) in [
        (
            ContractExpression::CFragment(CExpression::Variable("result".into())),
            crate::kernel::C_CONTRACT_RESULT_NAME,
            true,
            "result",
        ),
        (
            ContractExpression::CBinding("result".into()),
            "result",
            true,
            "result",
        ),
        (
            ContractExpression::CFragment(CExpression::Variable("bound".into())),
            "bound",
            false,
            "bound",
        ),
    ] {
        context.contract_result_in_scope = in_scope;
        let place = member(operand_name);
        let expression = ContractExpression::CUnary {
            operand: Box::new(ContractExpression::Field {
                base: Box::new(base),
                field: "value".into(),
                lowered: place.clone(),
                offset_bytes: 8,
            }),
            lowered: CExpression::AddressOf(Box::new(member("result"))),
        };
        let lowered = lowerer
            .lower_contract_expression_to_spec(&expression, &context)
            .expect("the selected member address lowers in the result scope");
        assert_eq!(
            lowered,
            SpecExpression::CExpression(CExpression::AddressOf(Box::new(member(expected)))),
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
    let state = CState::new();
    let snapshots = RecordedSnapshots::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let (lowerer, context) = fixed_state_elaboration(
        BTreeMap::new(),
        BTreeMap::new(),
        &state,
        BTreeMap::new(),
        BTreeMap::new(),
        None,
        &snapshots,
        SpecDefinitions::new(&predicates, &functions),
        BTreeSet::new(),
        parameter_pointer_element_widths(function.parameters()),
    );
    let pointer_add = CExpression::Add(
        Box::new(CExpression::Variable("p".into())),
        Box::new(CExpression::Variable("i".into())),
    );
    let cast = CExpression::Cast {
        expression: Box::new(pointer_add),
        target_type: CType::UInt64,
        integer_mode: crate::kernel::CIntegerCastMode::Standard,
        pointee_struct: None,
        pointee_volatile: false,
        pointee_constant: false,
        explicit_qualification: false,
    };
    let lowered = lowerer
        .lower_c_fragment_to_spec(&cast, &context)
        .expect("pointer arithmetic should lower");
    let SpecExpression::Cast(pointer, CType::UInt64) = lowered else {
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
                        SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                            index,
                        )))),
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
fn nested_snapshot_propositions_lower_with_small_frames_and_linear_visits() {
    std::thread::Builder::new()
        .name("small-stack-proposition-lowering".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = CState::new().with_local("x", int32(7));
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let mut snapshots = RecordedSnapshots::default();
            snapshots.insert(SnapshotSelector::Mark("before".into()), state.clone());
            let atom = || ClickProposition::Comparison {
                left: ContractExpression::At {
                    selector: SnapshotSelector::Mark("before".into()),
                    expression: Box::new(ContractExpression::CFragment(CExpression::Variable(
                        "x".into(),
                    ))),
                },
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(7))),
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
                    BTreeMap::from([("x".into(), int32(7))]),
                    BTreeMap::from([("x".into(), int32(9))]),
                    None,
                    &snapshots,
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
/// `at(...)` snapshot, including a loop's own entry, are refused.
#[test]
fn a_fixed_state_anywhere_in_a_measure_is_found() {
    let current = ContractExpression::CBinding("n".to_string());
    assert!(fixed_measure_state(&current).is_none());

    let old = ContractExpression::Subtract(
        Box::new(current.clone()),
        Box::new(ContractExpression::Old(Box::new(current.clone()))),
    );
    assert!(matches!(
        fixed_measure_state(&old),
        Some(FixedMeasureState::Old)
    ));

    let loop_entry = SnapshotSelector::ProgramPoint(ProgramPointRef {
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
    let found = fixed_measure_state(&at).expect("a snapshot in a call argument is a snapshot");
    let FixedMeasureState::At(selector) = &found else {
        panic!("the refusal names the snapshot, not `old`");
    };
    assert_eq!(selector, &loop_entry);
    assert_eq!(found.spelling(), "at(loop(0).entry, ...)");
}

#[test]
fn surface_binder_streams_refuse_before_another_producers_range() {
    let mut quantifier = SURFACE_QUANTIFIER_VARIABLE_CEILING - 1;
    assert_eq!(
        allocate_quantifier_variable(&mut quantifier),
        Ok(Variable(SURFACE_QUANTIFIER_VARIABLE_CEILING - 1)),
    );
    assert!(allocate_quantifier_variable(&mut quantifier).is_err());

    let last_algebraic_index = ((ALGEBRAIC_VARIABLE_CEILING - 1 - ALGEBRAIC_VARIABLE_BASE)
        / ALGEBRAIC_BINDER_STRIDE) as usize;
    assert!(algebraic_binder_variable(last_algebraic_index).is_ok());
    assert!(algebraic_binder_variable(last_algebraic_index + 1).is_err());
}

#[test]
fn captured_fold_identity_does_not_exhaust_the_surface_quantifier_stream() {
    let low = Variable(SURFACE_QUANTIFIER_VARIABLE_CEILING - 2);
    let high = Variable((1 << 43) + 17);
    let captured = crate::kernel::SpecIntegerExpression::Add(
        Box::new(crate::kernel::SpecIntegerExpression::Term(
            crate::kernel::IntegerTerm::var(low),
        )),
        Box::new(crate::kernel::SpecIntegerExpression::Term(
            crate::kernel::IntegerTerm::var(high),
        )),
    );
    assert_eq!(max_spec_integer_expression_variable(&captured), Some(low));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/lowering/annotations/tests.rs");
}

/// One walk's loop index agrees with the per-index walk it replaces at every
/// index, across nested, `for`, `do` and `if`-arm loops, and past the end.
#[test]
fn c0_loop_index_agrees_with_the_walk_at_every_loop() {
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
    let index = c0_loops_by_index(function.body());
    assert_eq!(index.len(), 6);
    for target in 0..index.len() + 2 {
        assert_eq!(
            index.get(target).and_then(Option::as_ref),
            c0_loop_by_index(function.body(), target),
            "loop({target})"
        );
    }
}
