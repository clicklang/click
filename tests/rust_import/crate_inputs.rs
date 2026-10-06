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
fn charon_adler2_locked_crate_reaches_owned_operand_boundary() {
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
        error.contains("assignment operator operand (by-value aggregates remain later work)"),
        "{error}"
    );
    assert!(!p.root.join("crate.ullbc").exists());
    assert!(!p.root.join("borrow.click.import.json.lock").exists());
}

#[test]
fn rust_crate_constructor_bodies_return_owned_field_values() {
    let p = Project::new("");
    let source = r#"
        pub mod inner {
            pub struct Value { pub a: u32, pub b: u32 }
            impl Default for Value { fn default() -> Self { Self { a: 1, b: 0 } } }
            impl Value { pub fn new() -> Self { Self::default() } }
        }
        pub fn entry() -> u32 { let v = inner::Value::new(); let moved = v; moved.a }
        pub fn second() -> u32 { let v = inner::Value::default(); v.b }
        pub fn make(x: u32) -> inner::Value { inner::Value { a: x, b: 7 } }
        pub fn argument(x: u32) -> u32 { let v = make(x); v.a }
        pub struct Token { pub n: u32 }
        impl Drop for Token { fn drop(&mut self) { self.n = 9; } }
        pub fn token() -> Token { Token { n: 4 } }
        pub fn token_entry() -> u32 { let v = token(); v.n }
        pub struct Packet { pub words: [u32; 4] }
        pub fn packet(x: u32) -> Packet { Packet { words: [x; 4] } }
        pub fn packet_entry(x: u32) -> u32 { let v = packet(x); v.words[3] }
    "#;
    fs::write(p.root.join("lib.rs"), source).unwrap();
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"lib.rs",
        "exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"demo","edition":"2021","features":[],"roots":["demo::entry","demo::second","demo::argument","demo::token_entry","demo::packet_entry"],"files":["lib.rs"]}
    })).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let record = "__rust_q_I4_demo_I5_inner_I5_Value";
    let default = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name.ends_with("_default"))
        .unwrap();
    let new = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name.ends_with("_I3_new"))
        .unwrap();
    let constructors = format!(
        "verifying \"lib.rs\"; struct {record} {}() {{ ensures result.a == 1u32; ensures result.b == 0u32; }} by {{ execute(); simp(); }}\nstruct {record} {}() {{ ensures result.a == 1u32; ensures result.b == 0u32; }} by {{ execute(); simp(); }}\nstruct {record} __rust_q_I4_demo_I4_make(uint32 x) {{ ensures result.a == x; ensures result.b == 7u32; }} by {{ execute(); simp(); }}",
        default.name, new.name
    );
    let proof = r#"
        void __rust_q_I4_demo_I5_Token_drop(struct __rust_q_I4_demo_I5_Token* self) { owns self->n; ensures self->n == 9u32; } by { execute(); simp(); }
        struct __rust_q_I4_demo_I5_Token __rust_q_I4_demo_I5_token() { ensures result.n == 4u32; } by { execute(); simp(); }
        uint32 __rust_q_I4_demo_I11_token_entry() { ensures result == 4u32; } by { execute(); simp(); }
        struct __rust_q_I4_demo_I6_Packet __rust_q_I4_demo_I6_packet(uint32 x) { ensures result.words[3] == x; } by { execute(); simp(); }
        uint32 __rust_q_I4_demo_I12_packet_entry(uint32 x) { ensures result == x; } by { execute(); simp(); }
        uint32 __rust_q_I4_demo_I5_entry() { ensures result == 1u32; } by { execute(); simp(); }
        uint32 __rust_q_I4_demo_I6_second() { ensures result == 0u32; } by { execute(); simp(); }
        uint32 __rust_q_I4_demo_I8_argument(uint32 x) { ensures result == x; } by { execute(); simp(); }
    "#;
    let proof = format!("{constructors}\n{proof}");
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for (before, after) in [
        ("result == 1u32", "result == 0u32"),
        ("result == 0u32", "result == 1u32"),
        ("result == x", "result != x"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&proof.replace(before, after), &prepared)
                .is_err()
        );
    }
    fs::write(p.root.join("borrow.click"), &proof).unwrap();
    let cli = p.cli(&["verify"]);
    assert!(
        cli.status.success(),
        "{}",
        String::from_utf8_lossy(&cli.stderr)
    );
    fs::write(
        p.root.join("lib.rs"),
        source.replace("a: 1, b: 0", "a: 9, b: 0"),
    )
    .unwrap();
    refresh_import(&p.config()).unwrap();
    let changed = load_import(&p.config()).unwrap();
    assert!(C0VerificationSession::new_program_prepared(&proof, &changed).is_err());
    C0VerificationSession::new_program_prepared(
        &proof
            .replace("result == 1u32", "result == 9u32")
            .replace("result.a == 1u32", "result.a == 9u32"),
        &changed,
    )
    .unwrap();
}

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_unchanged_constructor_returns_initialized_state() {
    let p = Project::new("");
    fs::write(
        p.root.join("lib.rs"),
        include_bytes!("../../design/charon-trial/adler2/src/lib.rs"),
    )
    .unwrap();
    fs::write(
        p.root.join("algo.rs"),
        include_bytes!("../../design/charon-trial/adler2/src/algo.rs"),
    )
    .unwrap();
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"lib.rs",
        "exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"adler2","edition":"2021","features":["std"],"roots":["adler2::Adler32::new"],"files":["lib.rs","algo.rs"]}
    })).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let record = &prepared.export().records[0].name;
    let default = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name.ends_with("_default"))
        .unwrap();
    let new = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name.ends_with("_I3_new"))
        .unwrap();
    let proof = format!(
        "verifying \"lib.rs\"; struct {record} {}() {{ ensures result.a == 1; ensures result.b == 0; }} by {{ execute(); simp(); }} struct {record} {}() {{ ensures result.a == 1; ensures result.b == 0; }} by {{ execute(); simp(); }}",
        default.name, new.name
    );
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("result.a == 1", "result.a == 0"),
            &prepared
        )
        .is_err()
    );
    fs::write(p.root.join("borrow.click"), &proof).unwrap();
    let cli = p.cli(&["verify"]);
    assert!(
        cli.status.success(),
        "{}",
        String::from_utf8_lossy(&cli.stderr)
    );
}
