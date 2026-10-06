use super::*;

fn crate_project() -> Project {
    let p = Project::new("");
    fs::create_dir(p.root.join("src")).unwrap();
    for (name, source) in [
        (
            "lib.rs",
            "pub mod left; pub mod right; mod unused; pub struct Value { pub n: u32 } impl Value { pub fn read(&self) -> u32 { self.n } } pub fn entry(v: &Value) -> u32 { left::read(v.read()) } pub fn left_read() -> u32 { 99 }",
        ),
        ("left.rs", "pub fn read(x: u32) -> u32 { x }"),
        ("right.rs", "pub fn read(x: u32) -> u32 { 7 }"),
        ("unused.rs", "pub fn not_reachable() -> u32 { 1 }"),
    ] {
        fs::write(p.root.join("src").join(name), source).unwrap();
    }
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu",
        "source":"src/lib.rs","exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"demo","edition":"2021","features":[],
            "roots":["demo::entry","demo::right::read","demo::left_read","demo::Value::read"],
            "files":["src/lib.rs","src/left.rs","src/right.rs","src/unused.rs"]}
    })).unwrap()).unwrap();
    p
}

#[test]
fn rust_crate_locks_all_compiler_inputs_and_preserves_qualified_calls() {
    let p = crate_project();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let functions = &prepared.export().functions;
    assert_eq!(functions.len(), 5);
    let names: std::collections::BTreeSet<_> = functions.iter().map(|f| &f.name).collect();
    assert_eq!(names.len(), 5);
    let proof = "verifying \"src/lib.rs\";\nuint32 __rust_q_I4_demo_I4_left_I4_read(uint32 x) { ensures result == x; } by { execute(); simp(); }\nuint32 __rust_q_I4_demo_I5_right_I4_read(uint32 x) { ensures result == 7; } by { execute(); simp(); }\nuint32 __rust_q_I4_demo_I9_left_read() { ensures result == 99; } by { execute(); simp(); }";
    let method = functions.iter().find(|f| f.name.contains("_T25_")).unwrap();
    let proof = format!(
        "{proof}\nuint32 {}(const struct __rust_q_I4_demo_I5_Value* self) {{ views self->n; ensures result == self->n; }} by {{ execute(); simp(); }}\nuint32 __rust_q_I4_demo_I5_entry(const struct __rust_q_I4_demo_I5_Value* v) {{ views v->n; ensures result == v->n; }} by {{ execute(); simp(); }}",
        method.name
    );
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    fs::write(p.root.join("borrow.click"), &proof).unwrap();
    let cli = p.cli(&["verify"]);
    assert!(
        cli.status.success(),
        "{}",
        String::from_utf8_lossy(&cli.stderr)
    );
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("result == 7", "result == x"),
            &prepared
        )
        .is_err()
    );
    let artifact = fs::read(p.root.join("crate.ullbc")).unwrap();
    let lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
    // Even a module with no translated body is part of the compiler closure.
    fs::write(
        p.root.join("src/unused.rs"),
        "pub fn not_reachable() -> u32 { 2 }",
    )
    .unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    refresh_import(&p.config()).unwrap();
    assert_ne!(
        load_import(&p.config()).unwrap().identity(),
        prepared.identity()
    );
    // Omitted and extra inputs are rejected before replacing existing outputs.
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["crate"]["files"]
        .as_array_mut()
        .unwrap()
        .push("extra.rs".into());
    fs::write(p.root.join("extra.rs"), "pub fn extra() {} ").unwrap();
    let fresh_artifact = fs::read(p.root.join("crate.ullbc")).unwrap();
    let fresh_lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    assert!(
        refresh_import(&p.config())
            .unwrap_err()
            .contains("source closure differs")
    );
    assert_eq!(
        fs::read(p.root.join("crate.ullbc")).unwrap(),
        fresh_artifact
    );
    assert_eq!(
        fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
        fresh_lock
    );
    config["crate"]["files"]
        .as_array_mut()
        .unwrap()
        .retain(|name| name != "extra.rs" && name != "src/unused.rs");
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    assert!(refresh_import(&p.config()).is_err());
    assert_eq!(
        fs::read(p.root.join("crate.ullbc")).unwrap(),
        fresh_artifact
    );
    assert_eq!(
        fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
        fresh_lock
    );
    assert!(!artifact.is_empty() && !lock.is_empty());
}

#[test]
fn rust_crate_rejects_escape_symlink_and_changed_configuration() {
    let p = crate_project();
    refresh_import(&p.config()).unwrap();
    let original = fs::read(p.config()).unwrap();
    for (field, value) in [
        ("edition", serde_json::json!("2024")),
        ("features", serde_json::json!(["std"])),
        ("roots", serde_json::json!(["demo::left_read"])),
    ] {
        let mut config: serde_json::Value = serde_json::from_slice(&original).unwrap();
        config["crate"][field] = value;
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(
            load_import(&p.config())
                .unwrap_err()
                .contains("lock differs")
        );
    }
    fs::write(p.config(), &original).unwrap();
    let mut config: serde_json::Value = serde_json::from_slice(&original).unwrap();
    config["crate"]["files"][1] = "../left.rs".into();
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    assert!(
        refresh_import(&p.config())
            .unwrap_err()
            .contains("inside the import directory")
    );
    fs::write(p.config(), &original).unwrap();
    #[cfg(unix)]
    {
        fs::rename(p.root.join("src/left.rs"), p.root.join("src/real-left.rs")).unwrap();
        std::os::unix::fs::symlink("real-left.rs", p.root.join("src/left.rs")).unwrap();
        assert!(
            refresh_import(&p.config())
                .unwrap_err()
                .contains("symlinks")
        );
    }
}

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_locked_crate_reaches_checked_trait_boundary() {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "lib.rs",
            include_bytes!("../../design/charon-trial/adler2/src/lib.rs").as_slice(),
        ),
        (
            "algo.rs",
            include_bytes!("../../design/charon-trial/adler2/src/algo.rs").as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"lib.rs",
        "exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"adler2","edition":"2021","features":["std"],"roots":["adler2::adler32_slice"],"files":["lib.rs","algo.rs"]}
    })).unwrap()).unwrap();
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(
        error.contains("source trait method outside Drop and assignment operators"),
        "{error}"
    );
    assert!(!p.root.join("crate.ullbc").exists());
    assert!(!p.root.join("borrow.click.import.json.lock").exists());
}
