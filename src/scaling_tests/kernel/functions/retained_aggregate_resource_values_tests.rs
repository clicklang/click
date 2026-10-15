// Scaling tests of `src/kernel/functions.rs` (module `retained_aggregate_resource_values_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn retained_resource_fields_preserve_lvalues_and_scale_with_expression() {
    let slot = Pointer {
        block: "local:frame:0:input".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointee = Pointer {
        block: "pointee".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = CValue::typed_pointer(pointee, CType::Int32Pointer);
    let layout = CAggregateLayout::new(
        8,
        8,
        vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
    );
    let field = CExpression::TypedLoad {
        pointer: Box::new(CExpression::Variable("input".into())),
        value_type: CType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let mut work = Vec::new();
    for size in [8, 32, 128, 512] {
        // Compare cold sessions at every size; retained pointer reads
        // otherwise reuse observations recorded by the first sample.
        let _session = crate::kernel::VerificationSession::enter();
        let mut entry = CState::new().with_memory(
            CMemory::new()
                .with_block(slot.block.clone(), 8)
                .store(slot.clone(), value.clone()),
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
        let resolve = |expression: &mut CExpression| {
            resolve_retained_aggregate_fields(
                &entry,
                &state,
                expression,
                true,
                &PureFactContext::new(),
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap();
        };
        let mut expression = field.clone();
        let (_, measured) =
            crate::instrumentation::measure_deterministic_work(|| resolve(&mut expression));
        work.push(measured);
        assert_eq!(expression, CExpression::Value(value.clone()));
        let address = CExpression::AddressOf(Box::new(field.clone()));
        let mut expression = address.clone();
        resolve(&mut expression);
        assert_eq!(
            expression, address,
            "an address must not become a retained value"
        );
        let mut expression = CExpression::Load(Box::new(field.clone()));
        resolve(&mut expression);
        assert_eq!(
            expression,
            CExpression::Load(Box::new(CExpression::Value(value.clone())))
        );
        assert!(!state.memory.has_block(&slot.block));
        assert!(state.resources().facts().is_empty());
    }
    assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
}
