use super::*;

#[test]
fn rust_default_is_native_charon_and_legacy_extraction_is_rejected() {
    let p = Project::new(SOURCE);
    let config: serde_json::Value = serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    assert_eq!(config["schema"], 3);
    assert!(config.get("backend").is_none());
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .all(|f| f.mir.is_some() && f.body.is_empty())
    );
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    let artifact = fs::read(p.root.join("borrow.ullbc")).unwrap();
    let lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
    for backend in [None, Some("legacy"), Some("charon")] {
        let mut old = config.clone();
        old["schema"] = serde_json::json!(2);
        if let Some(backend) = backend {
            old["backend"] = backend.into();
        }
        fs::write(p.config(), serde_json::to_vec(&old).unwrap()).unwrap();
        for error in [
            refresh_import(&p.config()).unwrap_err(),
            load_import(&p.config()).unwrap_err(),
        ] {
            assert!(error.contains("legacy extraction is retired"), "{error}");
        }
        assert_eq!(fs::read(p.root.join("borrow.ullbc")).unwrap(), artifact);
        assert_eq!(
            fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
            lock
        );
    }
}

#[test]
fn rust_default_conditional_simp_expansion_reverifies() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    let expanded =
        click::surface::expand_program_prepared_tactic_source_at(SIDECAR, &prepared, 8, 5).unwrap();
    C0VerificationSession::new_program_prepared(&expanded, &prepared)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn rust_native_aliases_use_the_same_backend_and_unknown_backends_fail_closed() {
    let p = Project::new(SOURCE);
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    for backend in ["charon", "charon-trial"] {
        let mut config = original.clone();
        config["backend"] = backend.into();
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        assert!(
            prepared
                .export()
                .functions
                .iter()
                .all(|f| f.mir.is_some() && f.body.is_empty())
        );
        C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    }
    let artifact = fs::read(p.root.join("borrow.ullbc")).unwrap();
    let lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
    let mut invalid = original;
    invalid["backend"] = "legacy".into();
    fs::write(p.config(), serde_json::to_vec(&invalid).unwrap()).unwrap();
    assert!(
        refresh_import(&p.config())
            .unwrap_err()
            .contains("unsupported Rust import")
    );
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("unsupported Rust import")
    );
    assert_eq!(fs::read(p.root.join("borrow.ullbc")).unwrap(), artifact);
    assert_eq!(
        fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
        lock
    );
}

#[test]
fn rust_refresh_is_reproducible_for_configs_sharing_an_artifact() {
    let p = Project::new(SOURCE);
    let second = p.root.join("second.click.import.json");
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["backend"] = "charon".into();
    fs::write(&second, serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let artifact = fs::read(p.root.join("borrow.ullbc")).unwrap();
    refresh_import(&second).unwrap();
    assert_eq!(fs::read(p.root.join("borrow.ullbc")).unwrap(), artifact);
    for config in [p.config(), second] {
        let prepared = load_import(&config).unwrap();
        C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    }
}
