use super::*;

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_default_is_native_charon_and_legacy_extraction_is_rejected() {
    let p = Project::legacy(SOURCE);
    let config: serde_json::Value = serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    assert_eq!(config["schema"], 3);
    assert!(config.get("backend").is_none());
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .all(|f| f.mir.is_some() && f.body.is_empty())
    );
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    let artifact = fs::read(p.artifact("borrow.rs")).unwrap();
    let lock = fs::read(p.lock_file()).unwrap();
    for backend in [None, Some("legacy"), Some("charon")] {
        let mut old = config.clone();
        old["schema"] = serde_json::json!(2);
        if let Some(backend) = backend {
            old["backend"] = backend.into();
        }
        fs::write(p.config(), serde_json::to_vec(&old).unwrap()).unwrap();
        for error in [p.refresh().unwrap_err(), p.prepared().unwrap_err()] {
            assert!(error.contains("legacy extraction is retired"), "{error}");
        }
        assert_eq!(fs::read(p.artifact("borrow.rs")).unwrap(), artifact);
        assert_eq!(fs::read(p.lock_file()).unwrap(), lock);
    }
}

#[test]
fn rust_default_conditional_simp_expansion_reverifies() {
    let p = gate_fixtures::project("basic", SOURCE);
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    let expanded =
        click::surface::expand_program_prepared_tactic_source_at(SIDECAR, &prepared, 8, 5).unwrap();
    C0VerificationSession::new_program_prepared(&expanded, &prepared)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn rust_import_pure_theorem_claim_labels_expand_and_reverify() {
    use click::surface::{ClickModuleSource, ClickProject};

    let p = gate_fixtures::project("basic", SOURCE);
    let prepared = p.prepared().unwrap();
    let source = format!(
        "{SIDECAR}\ntheorem mixed(n: int32) {{\n\
         ensures n == n by {{ simp(); }}\n\
         ensures ordered: n <= n by {{ simp(); }}\n\
         }}\n"
    );
    C0VerificationSession::new_program_prepared(&source, &prepared).unwrap();
    let project_for = |source: &str| {
        ClickProject::new(
            "borrow.click",
            [ClickModuleSource::new("borrow.click", source, [])],
        )
    };
    for label in ["mixed.ensures_0", "mixed.ordered"] {
        let expanded = click::surface::expand_program_prepared_claim_source_by_label(
            &source, &prepared, label,
        )
        .unwrap();
        assert_ne!(expanded, source);
        C0VerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
        let expanded = click::surface::expand_project_claim_source_by_label(
            &project_for(&source),
            &click::surface::ProgramInputs::program(&prepared),
            label,
        )
        .unwrap();
        C0VerificationSession::new_program_prepared_project(&project_for(&expanded), &prepared)
            .unwrap();
    }
    let invalid = source.replace("ensures n == n", "ensures n == n + 1");
    assert!(
        click::surface::expand_program_prepared_claim_source_by_label(
            &invalid,
            &prepared,
            "mixed.ensures_0",
        )
        .is_err()
    );
    assert!(
        click::surface::expand_project_claim_source_by_label(
            &project_for(&invalid),
            &click::surface::ProgramInputs::program(&prepared),
            "mixed.ensures_0"
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_native_aliases_use_the_same_backend_and_unknown_backends_fail_closed() {
    let p = Project::legacy(SOURCE);
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    for backend in ["charon", "charon-trial"] {
        let mut config = original.clone();
        config["backend"] = backend.into();
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        p.refresh().unwrap();
        let prepared = p.prepared().unwrap();
        assert!(
            prepared
                .export()
                .functions
                .iter()
                .all(|f| f.mir.is_some() && f.body.is_empty())
        );
        C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    }
    let artifact = fs::read(p.artifact("borrow.rs")).unwrap();
    let lock = fs::read(p.lock_file()).unwrap();
    let mut invalid = original;
    invalid["backend"] = "legacy".into();
    fs::write(p.config(), serde_json::to_vec(&invalid).unwrap()).unwrap();
    assert!(p.refresh().unwrap_err().contains("unsupported Rust import"));
    assert!(
        p.prepared()
            .unwrap_err()
            .contains("unsupported Rust import")
    );
    assert_eq!(fs::read(p.artifact("borrow.rs")).unwrap(), artifact);
    assert_eq!(fs::read(p.lock_file()).unwrap(), lock);
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_refresh_is_reproducible_for_configs_sharing_an_artifact() {
    let p = Project::legacy(SOURCE);
    let second = p.root.join("second.click.import.json");
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["backend"] = "charon".into();
    fs::write(&second, serde_json::to_vec(&config).unwrap()).unwrap();
    p.refresh().unwrap();
    let artifact = fs::read(p.artifact("borrow.rs")).unwrap();
    refresh_import(&second).unwrap();
    assert_eq!(fs::read(p.artifact("borrow.rs")).unwrap(), artifact);
    for config in [p.config(), second] {
        let prepared = load_import(&config).unwrap();
        C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    }
}
