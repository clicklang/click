use super::*;

#[test]
fn named_parameter_shadowing_ignores_unrelated_globals() {
    let mut baseline = None;
    for size in [0, 16, 128] {
        let state = globals(size);
        let value = CValue::typed_pointer(
            Pointer {
                block: "parameter-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::Int32Pointer,
        );
        let parameters = [syntax::C0Parameter::new(
            C0Type::Int32Pointer,
            "bytes".into(),
            None,
        )];
        let arguments = [CExpression::Value(value.clone())];
        let binding = ParameterBinding::new(&parameters, &arguments);
        let names = BTreeSet::from(["bytes".to_string()]);
        let ((values, arrays), work) = crate::instrumentation::measure_deterministic_work(|| {
            contract_environment_for_names(binding, &names, &state).unwrap()
        });
        assert_bytes(&values, &arrays, &value, CType::Int32);
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "{size} unrelated globals"
        );
    }
}
