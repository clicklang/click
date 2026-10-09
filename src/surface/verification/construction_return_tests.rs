use super::*;
use crate::kernel::*;

// This is a typed-frontend integration fixture, not C++ source admission.
// The source supplies nominal declarations only; the executable functions
// explicitly select the shared construction-return mode.
fn context(initialize_value: bool) -> CSourceContext<'static> {
    const DECLARATIONS: &str = "struct Node { int32* self; int32 value; };";
    let sources = CSourceContext::bundle(&[("construction.c", DECLARATIONS)]);
    let mut unit = parse_c_source_unit("construction.c", &sources, CTarget::SUPPORTED).unwrap();
    let nominal = unit.structs["Node"].clone();
    let layout = nominal.to_kernel_aggregate_layout();
    let destination = c_variable(C_CONTRACT_RESULT_NAME);
    let field = c_cast(
        c_pointer_offset_bytes(destination.clone(), 8),
        CType::Int32Pointer,
    );
    let factory = c_function(
        CType::Int32Pointer,
        "factory",
        vec![c_parameter("input", CType::Int32)],
        c_seq(
            c_typed_store(destination.clone(), field.clone(), CType::Int32Pointer),
            c_seq(
                if initialize_value {
                    c_typed_store(field, c_variable("input"), CType::Int32)
                } else {
                    c_skip()
                },
                c_return(destination.clone()),
            ),
        ),
    )
    .with_construction_return(layout.clone());
    let forward = c_function(
        CType::Int32Pointer,
        "forward",
        vec![c_parameter("input", CType::Int32)],
        c_seq(
            c_call_assign(C_CONTRACT_RESULT_NAME, "factory", vec![c_variable("input")]),
            c_return(destination),
        ),
    )
    .with_construction_return(layout.clone());
    let caller = c_function(
        CType::Int32,
        "probe",
        vec![c_parameter("input", CType::Int32)],
        c_seq(
            c_allocate_aggregate_destination("node", layout),
            c_seq(
                c_call_assign("node", "forward", vec![c_variable("input")]),
                c_return(c_load(c_typed_load(
                    c_variable("node"),
                    CType::Int32Pointer,
                ))),
            ),
        ),
    );
    let parameters = || {
        vec![syntax::C0Parameter::new(
            C0Type::Int32,
            "input".into(),
            None,
        )]
    };
    unit.functions = vec![
        syntax::C0Function::external(C0Type::Int32Pointer, "factory".into(), parameters())
            .with_struct_return("Node".into(), nominal.clone())
            .with_prelowered_kernel_function(factory),
        syntax::C0Function::external(C0Type::Int32Pointer, "forward".into(), parameters())
            .with_struct_return("Node".into(), nominal.clone())
            .with_prelowered_kernel_function(forward),
        syntax::C0Function::external(C0Type::Int32, "probe".into(), parameters())
            .with_prelowered_kernel_function(caller)
            .with_local_struct_values(BTreeMap::from([("node".into(), "Node".into())])),
    ];
    sources
        .parsed_units
        .borrow_mut()
        .insert("construction.c".into(), Arc::new(unit));
    sources
}

const PROOF: &str = r#"verifying "construction.c";
struct Node factory(int32 input) {
 ensures result.self == &result.value;
 ensures result.value == input;
} by { execute(); simp(); }
struct Node forward(int32 input) {
 ensures result.self == &result.value;
 ensures result.value == input;
} by { execute(); simp(); }
int32 probe(int32 input) {
 ensures result == input;
} by { execute(); simp(); }
"#;

#[test]
fn native_construction_return_contracts_forward_hidden_storage() {
    let sources = context(true);
    let (verified, environment) =
        verify_c0_sources_with_context(PROOF, &sources, None, None, None, None).unwrap();
    // Exercise the same retained-environment path as a selected proof edit.
    let _tables = crate::kernel::VerificationSession::resume();
    for name in ["factory", "forward", "probe"] {
        verify_c0_sources_with_context(
            PROOF,
            &sources,
            Some(VerificationTarget::Function(name.into())),
            Some(environment.clone().without_verified_function_rule(name)),
            None,
            None,
        )
        .unwrap();
    }
    let mut expanded = PROOF.to_string();
    for name in ["factory", "forward", "probe"] {
        let theorem = verified
            .iter()
            .find(|theorem| theorem.function_block.signature().name() == name)
            .unwrap();
        expanded = expanded.replacen(
            "by { execute(); simp(); }",
            &theorem.expanded_proof_source().unwrap(),
            1,
        );
    }
    verify_c0_sources_with_context(&expanded, &sources, None, None, None, None).unwrap();
}

// The hidden resource needs no written storage clause, but returning it must
// not mark an unwritten field initialized. Keep the value claim independent
// of the fields so this exercises construction completion itself.
#[test]
fn native_construction_return_contracts_require_complete_initialization() {
    let safety_only = r#"verifying "construction.c";
struct Node factory(int32 input) { ensures input == input; } by { execute(); simp(); }
"#;
    let sources = context(true);
    verify_c0_sources_with_context(safety_only, &sources, None, None, None, None).unwrap();
    let sources = context(false);
    assert!(verify_c0_sources_with_context(safety_only, &sources, None, None, None, None).is_err());
}
