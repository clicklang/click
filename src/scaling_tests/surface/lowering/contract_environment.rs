use super::*;

#[test]
fn named_parameter_shadowing_ignores_unrelated_globals() {
    let mut baseline = None;
    for size in [0, 16, 128] {
        let state = globals(size);
        let value = ProgramValue::typed_pointer(
            Pointer {
                block: "parameter-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::Int32Pointer,
        );
        let parameters = [crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "bytes".into(),
            None,
        )];
        let arguments = [ProgramExpression::Value(value.clone())];
        let binding = ParameterBinding::new(&parameters, &arguments);
        let names = BTreeSet::from(["bytes".to_string()]);
        let ((values, arrays), work) = crate::instrumentation::measure_deterministic_work(|| {
            contract_environment_for_names(binding, &names, &state).unwrap()
        });
        assert_bytes(&values, &arrays, &value, ProgramType::Int32);
        assert_eq!(
            work,
            *baseline.get_or_insert(work),
            "{size} unrelated globals"
        );
    }
}
