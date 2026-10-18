// Scaling tests of `src/kernel/spec.rs` (module `aggregate_value_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn logical_fields_are_bounded_and_do_not_grant_pointer_access() {
    use crate::kernel::{CAggregateField, CAggregateLayout};
    let slot = Pointer {
        block: "local:frame:0:input".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let layout = CAggregateLayout::new(4, 4, vec![CAggregateField::new("value", 0, CType::Int32)]);
    let projection = SpecExpression::AggregateFieldValue {
        parameter: "input".to_string(),
        pointer: Box::new(SpecExpression::CExpression(CExpression::Variable(
            "input".to_string(),
        ))),
        value_type: CType::Int32,
    };
    let mut samples = Vec::new();
    for size in [8, 32, 128] {
        let mut entry = CState::new().with_memory(
            CMemory::new()
                .with_block(slot.block.clone(), 4)
                .store(slot.clone(), int32(7)),
        );
        entry
            .locals
            .set_aggregate_object_at("input".to_string(), layout.clone(), slot.clone());
        for i in 0..size {
            entry = entry.with_local(format!("unrelated_{i}"), int32(i));
        }
        let state = entry
            .clone()
            .with_memory(entry.memory.clone().without_local_block(&slot.block));
        let evaluate = |expression: &SpecExpression| {
            evaluate_spec_expression_paths_with_loop_entry_in(
                &state,
                expression,
                Some(&entry),
                &PureFactContext::new(),
                &mut SpecEvaluation::logical(&mut ExecutionBudget::beside_live_state()),
            )
            .unwrap()
        };
        let (values, work) =
            crate::instrumentation::measure_deterministic_work(|| evaluate(&projection));
        assert_eq!(values.len(), 1);
        assert_eq!(values[0].value, int32(7));
        assert!(values[0].obligations.is_empty());
        samples.push(work);
        let ordinary = SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(CValue::pointer(slot.clone()))),
            value_type: CType::Int32,
        };
        let paths = evaluate(&ordinary);
        assert_eq!(paths.len(), 1);
        assert!(paths[0].obligations.is_empty());
        assert!(!PureFactContext::new().proves_memory_read_defined(
            state.memory(),
            &slot,
            CType::Int32,
        ));
        let forged = SpecExpression::AggregateFieldValue {
            parameter: "input".to_string(),
            pointer: Box::new(SpecExpression::Value(CValue::pointer(slot.clone()))),
            value_type: CType::Int32,
        };
        assert!(evaluate(&forged).is_empty());
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
