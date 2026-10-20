use super::*;

const ARTIFACT: &[u8] = include_bytes!(
    "../../../../design/charon-trial/option-values/.click/option_values/options.rs.ullbc"
);
const SOURCE: &[u8] = include_bytes!("../../../../design/charon-trial/option-values/options.rs");

fn decode_options(artifact: &ExtractionArtifact) -> Result<out::RustExport, String> {
    let config: serde_json::Value = serde_json::from_slice(include_bytes!(
        "../../../../design/charon-trial/option-values/click.project.json"
    ))
    .unwrap();
    let config = serde_json::from_value(config["units"]["option_values"]["crate"].clone()).unwrap();
    let sources = BTreeMap::from([("options.rs".into(), SOURCE.to_vec())]);
    decode_crate(
        &serde_json::to_vec(artifact).unwrap(),
        "options.rs",
        SOURCE,
        Some(&config),
        Some(&sources),
    )
}

fn named<'a>(krate: &'a mut a::TranslatedCrate, method: &str) -> &'a mut a::FunDecl {
    krate
        .fun_decls
        .iter_mut()
        .find(|f| {
            matches!(f.item_meta.name.name.last(),
                Some(a::PathElem::Ident(name, _)) if name == method)
        })
        .unwrap()
}

/// `?` is rewritten only for the library's own `branch` and
/// `from_residual` on `Option` and its own `ControlFlow`: an unsafe,
/// renamed, relocated or re-signed declaration is refused rather than read
/// as `?`.
#[test]
fn charon_option_try_rejects_forged_library_declarations() {
    let artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
    let export = decode_options(&artifact).unwrap();
    let plus_one = export
        .functions
        .iter()
        .find(|f| f.name.ends_with("I8_plus_one"))
        .unwrap();
    assert!(
        plus_one
            .mir
            .as_ref()
            .unwrap()
            .blocks
            .iter()
            .all(|block| !matches!(block.terminator, T::Call { .. })),
        "`?` leaves no library call"
    );
    for mutation in 0..5 {
        let mut artifact: ExtractionArtifact = serde_json::from_slice(ARTIFACT).unwrap();
        let krate = &mut artifact.data.translated;
        match mutation {
            0 => named(krate, "branch").signature.is_unsafe = true,
            1 => {
                let a::FunSource::TraitImpl { trait_ref, .. } = &named(krate, "branch").src else {
                    panic!()
                };
                let id = trait_ref.id;
                krate.trait_decls[id].item_meta.name.name[0] =
                    a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
            }
            2 => {
                let a::FunSource::TraitImpl { impl_ref, .. } = &named(krate, "from_residual").src
                else {
                    panic!()
                };
                let id = impl_ref.id;
                krate.trait_impls[id].item_meta.name.name[0] =
                    a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
                let from_residual = named(krate, "from_residual");
                from_residual.item_meta.name.name[0] =
                    a::PathElem::Ident("impostor".into(), a::Disambiguator::ZERO);
            }
            3 => {
                krate
                    .type_decls
                    .iter_mut()
                    .find(|t| t.item_meta.diagnostic_item.as_deref() == Some("ControlFlow"))
                    .unwrap()
                    .item_meta
                    .diagnostic_item = None;
            }
            4 => {
                let from_residual = named(krate, "from_residual");
                from_residual.signature.output = from_residual.signature.inputs[0].clone();
            }
            _ => unreachable!(),
        }
        let error = decode_options(&artifact).expect_err("a forged `?` declaration");
        // A renamed `Try` makes `branch` an ordinary library call, refused
        // as one; every other forgery is refused as a `?`.
        assert!(
            mutation == 1 || error.contains("`?`"),
            "mutation {mutation}: {error}"
        );
    }
}
