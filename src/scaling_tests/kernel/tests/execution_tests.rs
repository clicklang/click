// Scaling tests of `src/kernel/tests/execution_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Selecting a verified loop rule reads each required assumption through an
/// indexed lookup, so the work is charged to the rule's own prerequisites and
/// does not grow with the unrelated ambient facts in scope at the loop.
#[test]
fn verified_loop_rule_selection_is_flat_in_unrelated_ambient_facts() {
    let (statement, base_rule) = prerequisite_loop_rule_fixture();
    let state = CState::new().with_local("i", int32(0));
    let guard = loop_rule_guard(1);
    let mut applicable = base_rule.clone();
    applicable.required_assumptions = PureFactContext::new().assume_condition(guard.clone(), true);
    let mut inapplicable = base_rule;
    inapplicable.required_assumptions =
        PureFactContext::new().assume_condition(loop_rule_guard(2), true);
    // The inapplicable rule comes first, so every lookup rejects one rule's
    // prerequisite and accepts the other's.
    let environment =
        CExecutionEnvironment::new().with_verified_loop_rules([inapplicable, applicable]);

    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_condition(guard.clone(), true);
        for index in 0..size as u32 {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(u64::from(500_000 + index))),
                    Bitvector32Term::Constant(index),
                ),
                true,
            );
        }
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            environment
                .applicable_verified_loop_rule(&state, &statement, &assumptions)
                .is_some()
        });
        assert!(selected, "the applicable rule should still be selected");
        assert_eq!(assumptions.pure_facts().len(), size + 1);
        assert!(
            work < 64,
            "selection work must stay bounded by the rules' own prerequisites: {work}"
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 16, "{samples:?}");
    }
}

// The back-edge closer must extend its checked assumptions once per member,
// rather than rebuilding the growing guard prefix for every declaration.
#[test]
fn invariant_back_edge_context_extension_scales_with_members_not_ambient_facts() {
    let state = CState::new().with_local("i", int32(Bitvector32Term::Variable(Variable(912_346))));
    let mut samples = Vec::new();
    for size in [8usize, 16, 32] {
        let checks = (0..size)
            .map(|index| {
                CLoopInvariantCheck::new(
                    SpecProposition::Comparison {
                        left: SpecExpression::CExpression(c_variable("i")),
                        operator: CComparisonOperator::LessEqual,
                        right: SpecExpression::Value(int32(1000 + index as u32)),
                    },
                    None,
                    Some(format!("member {index}")),
                )
            })
            .collect::<Vec<_>>();
        let mut ambient_samples = Vec::new();
        for ambient in [0usize, 128, 512] {
            let mut assumptions = PureFactContext::new();
            for index in 0..ambient {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let (goals, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_loop_invariant_obligations_at_back_edge(&state, &state, &checks, &assumptions)
                    .expect("all explicit members lower")
            });
            let entries = crate::kernel::reasoning::path_facts::context_rebuild_entries() - before;
            assert_eq!(goals.len(), size);
            assert!(
                entries <= 4 * size,
                "{size} members rebuilt {entries} entries"
            );
            assert!(goals.iter().enumerate().all(|(index, goal)| goal.context()
                == Some(format!("member {index}").as_str())
                && goal.introductions().is_some()));
            ambient_samples.push((entries, work));
        }
        assert!(
            ambient_samples.windows(2).all(|pair| pair[0] == pair[1]),
            "ambient facts changed closer work: {ambient_samples:?}"
        );
        samples.push(ambient_samples[0]);
    }
    for pair in samples.windows(2) {
        assert!(pair[1].0 <= 2 * pair[0].0 + 8, "{samples:?}");
        // The generated certificate explicitly contains its guard prefixes;
        // context insertion itself stays linear in the declared members.
        assert!(pair[1].1 <= 5 * pair[0].1 + 64, "{samples:?}");
    }
}

/// A zero-filled automatic array's declaration, a load of a written field,
/// of a zero one, and a store then a load, cost the same whatever the
/// array's length, and every load is exact. The declaration used to store
/// every field of every element.
#[test]
fn a_zero_filled_automatic_array_costs_the_same_whatever_its_length() {
    let samples = [100u32, 10_000, 1_000_000].map(|length| {
        let _session = crate::kernel::VerificationSession::enter();
        let statement = zero_filled_node_array(length, &[(20, int32(7), CType::Int32)]);
        let (state, declaration_work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_declaration(&CState::new(), &statement)
        });
        let last = 16 * (length - 1);
        let (loads, load_work) = crate::instrumentation::measure_deterministic_work(|| {
            let stored = execute_declaration(
                &state,
                &c_typed_store(
                    c_pointer_offset_bytes(c_variable("items"), last),
                    c_int32_literal(9),
                    CType::Int32,
                ),
            );
            [
                load_items_field(&state, 20, CType::Int32),
                load_items_field(&state, last, CType::Int32),
                load_items_field(&state, last + 4, CType::UInt8),
                load_items_field(&stored, last, CType::Int32),
                load_items_field(&stored, last - 16, CType::Int32),
            ]
        });
        let value = CExpressionOutcome::Value;
        assert_eq!(
            loads,
            [
                value(int32(7)),
                value(int32(0)),
                value(uint8(0)),
                value(int32(9)),
                value(int32(0)),
            ],
            "[{length}] reads its initializer"
        );
        (
            length,
            declaration_work,
            load_work,
            state.memory().cells.representation_len(),
        )
    });
    let (_, declaration_work, load_work, entries) = samples[0];
    assert!(
        samples
            .iter()
            .all(|sample| (sample.1, sample.2, sample.3) == (declaration_work, load_work, entries)),
        "a zero-filled declaration's cost depends on the array's length (length, declaration \
         work, load work, cell entries): {samples:?}"
    );
}
