// Scaling tests of `src/kernel/memory_provenance.rs` (module `condition_fact_graph_equivalence_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn condition_fact_graph_queries_scale_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let sum = |value| Bitvector32Term::add(value, Bitvector32Term::Constant(1));
        let source = less_than(sum(var(0)), var(9000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context =
                context.assume_condition(ConditionTerm::equal(var(index), var(index + 1)), true);
        }
        let _scope = context.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                let target = less_than(sum(var(index)), var(9000));
                assert!(c_condition_facts_equivalent_for_memory_resolution(
                    &source, &target, &context,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 300 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn failed_check_cell_capture_is_bounded_and_ignores_unrelated_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: "diagnostic-access".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory =
        crate::kernel::intern_c_memory(CMemory::new().with_block(base.block.clone(), 128).store(
            Pointer::symbolic(Variable(982_000)),
            CValue::Int32(Bitvector32Term::Constant(9)),
        ));
    let mut samples = Vec::new();
    for size in [8u64, 32, 128, 512] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(var(990_000 + index), Bitvector32Term::Constant(7)),
                true,
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_bounded_cell_walk_diagnostics(|| {
                for index in 0..32 {
                    let (_, stop) = memory_dag_cell_source_with_stop(
                        &memory,
                        &base.offset_by_bytes(index * 4),
                        4,
                        &context,
                        true,
                    )
                    .unwrap();
                    assert!(!matches!(stop, CellWalkStop::OldestRecorded));
                }
                let observations = take_transport_cell_walk_diagnostics();
                assert_eq!(observations.len(), 16);
                assert!(observations.iter().all(|walk| walk.bytes == 4));
            });
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}
