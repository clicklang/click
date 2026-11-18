// Scaling tests of `src/surface/proof/smart_closures.rs` (module `synthesized_literal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn speculative_solve_premise_spelling_declines_large_components_without_rendering() {
    let function = syntax::parse_function("int32 noop() { return 0; }").unwrap();
    let state = ExecutionState::new();
    let retained_states = RecordedStates::new();
    let surfaces = SurfacePropositionMap::default();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let proof = Proof::for_fixed_state_goal(
        "speculative premise rendering",
        0,
        &[],
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::constant(0)),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        ),
        ParameterBinding::new(function.parameters(), &[]),
        &state,
        &state,
        &retained_states,
        &surfaces,
        SpecDefinitions::new(&predicates, &functions),
        &theorems,
        &[],
    );
    for size in [128, 512, 2048, 8192] {
        let premises = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(Variable(8_179_000 + index))),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::resolve_solve_premises(&(proof), &premises, &[])
        });
        assert!(
            result.is_none(),
            "an oversized speculative component must be declined"
        );
        assert_eq!(work, 0, "size {size}: no candidate should be rendered");
    }
}

#[test]
fn reflexive_pointer_metadata_does_not_search_state_history() {
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let pointer = Address::symbolic(Variable(8_179_830));
    let state = ExecutionState::new().with_local("p", ProgramValue::pointer(pointer.clone()));
    let reflexive = Proposition::ConditionIs(
        ConditionTerm::AddressEqual(Box::new(pointer.clone()), Box::new(pointer)),
        true,
    );
    let equivalent = Proposition::Not(Box::new(match &reflexive {
        Proposition::ConditionIs(condition, _) => {
            Proposition::ConditionIs(condition.clone(), false)
        }
        _ => unreachable!(),
    }));
    let facts = [reflexive.clone(), equivalent.clone()];
    let surfaces = SurfacePropositionMap::default();
    for size in [4usize, 16, 64, 256] {
        let mut retained_states = RecordedStates::new();
        for index in 0..size {
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Entry,
                },
                state.clone(),
            );
        }
        let anchor = ProgramPointRef {
            region: CodeRegionRef::Region(size - 1),
            kind: ProgramPointKind::Entry,
        };
        let root = Proof::for_fixed_state_goal_with_requirements(
            "reflexive pointer metadata",
            0,
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ParameterBinding::default(),
            FixedStateFrame::new(&state, &state, None, &retained_states),
            Some(&anchor),
            &surfaces,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
            &[],
            &[],
        );
        for fact in &facts {
            let ((surface, events), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    crate::instrumentation::collect(|| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            &(root),
                            &surfaces,
                            Some(&anchor),
                            fact,
                        )
                    })
                });
            assert!(surface.is_none());
            assert!(work <= 32, "{size} states: {work} work");
            assert!(
                !events.iter().any(|event| matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name.starts_with("solve premise surface"))),
                "metadata must not walk history"
            );
            assert!(
                root.facts().contains(fact),
                "search leaves the kernel fact available"
            );
        }
    }
}
