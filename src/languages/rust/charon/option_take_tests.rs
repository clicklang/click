use super::*;

const ARTIFACT: &[u8] = include_bytes!(
    "../../../../design/charon-trial/option-take/.click/captures/option_take/take.rs.ullbc"
);
const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/option-take/take.rs");

fn decode_take(artifact: &ExtractionArtifact) -> Result<out::RustExport, String> {
    let config: serde_json::Value = serde_json::from_slice(include_bytes!(
        "../../../../design/charon-trial/option-take/click.project.json"
    ))
    .unwrap();
    let config = serde_json::from_value(config["units"]["option_take"]["crate"].clone()).unwrap();
    let sources = BTreeMap::from([("take.rs".into(), SOURCE.to_vec())]);
    decode_crate(
        &serde_json::to_vec(artifact).unwrap(),
        "take.rs",
        SOURCE,
        Some(&config),
        Some(&sources),
    )
}

fn take(krate: &mut a::TranslatedCrate) -> &mut a::FunDecl {
    krate
        .fun_decls
        .iter_mut()
        .find(|f| {
            matches!(f.item_meta.name.name.last(),
                Some(a::PathElem::Ident(name, _)) if name == "take")
        })
        .unwrap()
}

/// `take` of an option of a box is rewritten, and of a scalar calls the
/// library's `Option::take<T>`, only for the library's own `Option::take` at
/// its declared signature: an unsafe, re-signed or regenericized declaration
/// is refused rather than read as the library's.
#[test]
fn charon_option_take_rejects_forged_library_declarations() {
    let artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
    let export = decode_take(&artifact).unwrap();
    let library_take = crate::languages::rust::names::qualified_name(["Option", "take"]);
    let calls = export
        .functions
        .iter()
        .flat_map(|f| f.mir.iter().flat_map(|mir| &mir.blocks))
        .filter_map(|block| match &block.terminator {
            T::Call {
                function: out::MirCallee::Direct(function),
                ..
            } => Some(function.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        calls
            .iter()
            .any(|function| function.starts_with(&library_take)),
        "a scalar `take` calls the library's contract: {calls:?}"
    );
    // The box's free names its record's crate, `option_take`.
    assert!(
        calls.iter().all(|function| !function.contains("take")
            || function.contains("Box")
            || function.starts_with(&library_take)),
        "no other `take` call remains: {calls:?}"
    );
    for mutation in 0..4 {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let callee = take(&mut artifact.data.translated);
        match mutation {
            0 => callee.signature.is_unsafe = true,
            1 => callee.signature.output = callee.signature.inputs[0].clone(),
            2 => callee.signature.inputs[0] = callee.signature.output.clone(),
            3 => callee.src = a::FunSource::AdtConstructor,
            _ => unreachable!(),
        }
        let error = decode_take(&artifact).expect_err("a forged `take` declaration");
        assert!(
            error.contains("`Option::take`"),
            "mutation {mutation}: {error}"
        );
    }
}
