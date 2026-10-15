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
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_crate_locks_all_compiler_inputs_and_preserves_qualified_calls() {
    let p = crate_project();
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    let functions = &prepared.export().functions;
    assert_eq!(functions.len(), 5);
    let names: std::collections::BTreeSet<_> = functions.iter().map(|f| &f.name).collect();
    assert_eq!(names.len(), 5);
    assert!(functions.iter().any(|f| f.name.contains("_T25_")));
    let proof = "verifying \"src/lib.rs\";\nfn demo::left::read(x: u32) -> u32 { ensures result == x; } by { execute(); simp(); }\nfn demo::right::read(x: u32) -> u32 { ensures result == 7; } by { execute(); simp(); }\nfn demo::left_read() -> u32 { ensures result == 99; } by { execute(); simp(); }\nimpl demo::Value { fn read(&self) -> u32 { views self.n; ensures result == self.n; } by { execute(); simp(); } }\nfn demo::entry(v: &demo::Value) -> u32 { views v.n; ensures result == v.n; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(proof, &prepared).unwrap();
    fs::write(p.root.join("borrow.click"), proof).unwrap();
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
    let artifact = fs::read(p.artifact("crate.rs")).unwrap();
    let lock = fs::read(p.lock_file()).unwrap();
    // Even a module with no translated body is part of the compiler closure.
    fs::write(
        p.root.join("src/unused.rs"),
        "pub fn not_reachable() -> u32 { 2 }",
    )
    .unwrap();
    assert!(p.prepared().unwrap_err().contains("lock differs"));
    p.refresh().unwrap();
    assert_ne!(p.prepared().unwrap().identity(), prepared.identity());
    // Omitted and extra inputs are rejected before replacing existing outputs.
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["crate"]["files"]
        .as_array_mut()
        .unwrap()
        .push("extra.rs".into());
    fs::write(p.root.join("extra.rs"), "pub fn extra() {} ").unwrap();
    let fresh_artifact = fs::read(p.artifact("crate.rs")).unwrap();
    let fresh_lock = fs::read(p.lock_file()).unwrap();
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    let mismatch = p.refresh().unwrap_err();
    assert!(mismatch.contains("source closure differs"), "{mismatch}");
    assert!(
        mismatch.contains("missing from `crate.files`: none"),
        "{mismatch}"
    );
    assert!(
        mismatch.contains("extra in `crate.files`: \"extra.rs\""),
        "{mismatch}"
    );
    assert_eq!(fs::read(p.artifact("crate.rs")).unwrap(), fresh_artifact);
    assert_eq!(fs::read(p.lock_file()).unwrap(), fresh_lock);

    config["crate"]["files"]
        .as_array_mut()
        .unwrap()
        .retain(|name| name != "extra.rs" && name != "src/unused.rs");
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    let missing = p.refresh().unwrap_err();
    assert!(missing.contains("crate input check failed"), "{missing}");
    assert!(
        missing.contains("crate.files") && missing.contains("src/unused.rs"),
        "{missing}"
    );
    assert_eq!(fs::read(p.artifact("crate.rs")).unwrap(), fresh_artifact);
    assert_eq!(fs::read(p.lock_file()).unwrap(), fresh_lock);

    assert!(!artifact.is_empty() && !lock.is_empty());
}

#[test]
#[ignore = "nightly: 15s in the parallel gate"]
fn rust_crate_rejects_escape_symlink_and_changed_configuration() {
    let p = crate_project();
    p.refresh().unwrap();
    let original = fs::read(p.config()).unwrap();
    for (field, value) in [
        ("edition", serde_json::json!("2024")),
        ("features", serde_json::json!(["std"])),
        ("roots", serde_json::json!(["demo::left_read"])),
    ] {
        let mut config: serde_json::Value = serde_json::from_slice(&original).unwrap();
        config["crate"][field] = value;
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(p.prepared().unwrap_err().contains("lock differs"));
    }
    fs::write(p.config(), &original).unwrap();
    let mut config: serde_json::Value = serde_json::from_slice(&original).unwrap();
    config["crate"]["files"][1] = "../left.rs".into();
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    assert!(
        p.refresh()
            .unwrap_err()
            .contains("inside the import directory")
    );
    fs::write(p.config(), &original).unwrap();
    #[cfg(unix)]
    {
        fs::rename(p.root.join("src/left.rs"), p.root.join("src/real-left.rs")).unwrap();
        std::os::unix::fs::symlink("real-left.rs", p.root.join("src/left.rs")).unwrap();
        assert!(p.refresh().unwrap_err().contains("symlinks"));
    }
}

#[test]
#[ignore = "requires the pinned live Charon extractor"]
fn charon_adler2_locked_crate_imports_compute_and_proves_constants() {
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
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    let mut proof = String::from("verifying \"lib.rs\";\nimpl adler2::Adler32 {\n");
    for (suffix, name, ty, value) in [
        ("_I3_MOD", "MOD", "u32", "65521u32"),
        ("_I10_CHUNK_SIZE", "CHUNK_SIZE", "usize", "22208u64"),
    ] {
        assert!(
            prepared
                .export()
                .functions
                .iter()
                .any(|f| f.name.ends_with(&format!("_I7_compute{suffix}")))
        );
        proof.push_str(&format!(
            "fn compute::{name}() -> {ty} {{ ensures result == {value}; }} by {{ execute(); simp(); }}\n"
        ));
    }
    proof.push_str("}\n");
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .any(|f| f.name.ends_with("_I7_compute") && f.mir.is_some())
    );
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("65521u32", "65520u32"),
            &prepared
        )
        .is_err()
    );
    assert!(p.artifact("crate.rs").exists());
    assert!(p.lock_file().exists());
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
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
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    let constructors = "verifying \"lib.rs\";
        impl Default for demo::inner::Value { fn default() -> demo::inner::Value { ensures result.a == 1u32; ensures result.b == 0u32; } by { execute(); simp(); } }
        impl demo::inner::Value { fn new() -> demo::inner::Value { ensures result.a == 1u32; ensures result.b == 0u32; } by { execute(); simp(); } }
        fn demo::make(x: u32) -> demo::inner::Value { ensures result.a == x; ensures result.b == 7u32; } by { execute(); simp(); }";
    let proof = r#"
        impl Drop for demo::Token { fn drop(&mut self) { owns self.n; ensures self.n == 9u32; } by { execute(); simp(); } }
        fn demo::token() -> demo::Token { ensures result.n == 4u32; } by { execute(); simp(); }
        fn demo::token_entry() -> u32 { ensures result == 4u32; } by { execute(); simp(); }
        fn demo::packet(x: u32) -> demo::Packet { ensures result.words[3] == x; } by { execute(); simp(); }
        fn demo::packet_entry(x: u32) -> u32 { ensures result == x; } by { execute(); simp(); }
        fn demo::entry() -> u32 { ensures result == 1u32; } by { execute(); simp(); }
        fn demo::second() -> u32 { ensures result == 0u32; } by { execute(); simp(); }
        fn demo::argument(x: u32) -> u32 { ensures result == x; } by { execute(); simp(); }
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
    p.refresh().unwrap();
    let changed = p.prepared().unwrap();
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
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    assert_eq!(
        prepared.export().records[0].name,
        "__rust_q_I6_adler2_I7_Adler32"
    );
    let proof = "verifying \"lib.rs\"; impl Default for adler2::Adler32 { fn default() -> adler2::Adler32 { ensures result.a == 1; ensures result.b == 0; } by { execute(); simp(); } } impl adler2::Adler32 { fn new() -> adler2::Adler32 { ensures result.a == 1; ensures result.b == 0; } by { execute(); simp(); } }";
    C0VerificationSession::new_program_prepared(proof, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("result.a == 1", "result.a == 0"),
            &prepared
        )
        .is_err()
    );
    fs::write(p.root.join("borrow.click"), proof).unwrap();
    let cli = p.cli(&["verify"]);
    assert!(
        cli.status.success(),
        "{}",
        String::from_utf8_lossy(&cli.stderr)
    );
}

#[test]
#[ignore = "nightly: 20s in the parallel gate"]
fn rust_crate_owned_operator_operands_copy_and_move_independently() {
    let p = Project::new("");
    let source = r#"
        #[derive(Copy, Clone)]
        pub struct Packet { pub words: [u32; 4] }
        impl core::ops::AddAssign<Self> for Packet {
            fn add_assign(&mut self, other: Self) {
                self.words[0] += other.words[0];
                self.words[1] += other.words[1];
                self.words[2] += other.words[2];
                self.words[3] += other.words[3];
            }
        }
        pub fn entry(x: u32) -> u32 {
            let rhs = Packet { words: [x; 4] };
            let saved = rhs;
            let mut lhs = Packet { words: [0; 4] };
            lhs += rhs;
            lhs.words[0] = 9;
            saved.words[3]
        }
        pub struct Token { pub n: u32 }
        impl Drop for Token { fn drop(&mut self) { self.n = 9; } }
        pub fn consume_token(token: Token) -> u32 { token.n }
        pub fn drop_argument(x: u32) -> u32 { consume_token(Token { n: x }) }
        pub struct Value { pub n: u32 }
        pub fn consume(mut value: Value) -> u32 { value.n = 9; value.n }
        pub fn moving(x: u32) -> u32 { let value = Value { n: x }; consume(value) }
        pub fn copy_parameter(mut packet: Packet) -> u32 { packet.words[0] = 9; packet.words[0] }
        pub fn independent(x: u32) -> u32 {
            let packet = Packet { words: [x; 4] };
            let _result = copy_parameter(packet);
            packet.words[0]
        }
    "#;
    fs::write(p.root.join("lib.rs"), source).unwrap();
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"lib.rs",
        "exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"demo","edition":"2021","features":[],"roots":["demo::entry","demo::moving","demo::independent","demo::drop_argument"],"files":["lib.rs"]}
    })).unwrap()).unwrap();
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .any(|f| f.name.contains("_add_assign_value_"))
    );
    let mut clauses = String::from("owns self.words[0..4];");
    for index in 0..4 {
        clauses.push_str(&format!("requires self.words[{index}] <= 1000u32; requires other.words[{index}] <= 1000u32; ensures self.words[{index}] == old(self.words[{index}]) + other.words[{index}];"));
    }
    let proof = format!(
        r#"verifying "lib.rs";
        impl AddAssign<Self> for demo::Packet {{ fn add_assign(&mut self, other: demo::Packet) {{ {clauses} }} by {{ execute(); simp(); }} }}
        fn demo::entry(x: u32) -> u32 {{ requires x <= 1000u32; ensures result == x; }} by {{ execute(); simp(); }}
        fn demo::consume(value: demo::Value) -> u32 {{ ensures result == 9u32; }} by {{ execute(); simp(); }}
        fn demo::moving(x: u32) -> u32 {{ ensures result == 9u32; }} by {{ execute(); simp(); }}
        fn demo::copy_parameter(packet: demo::Packet) -> u32 {{ ensures result == 9u32; }} by {{ execute(); simp(); }}
        fn demo::independent(x: u32) -> u32 {{ ensures result == x; }} by {{ execute(); simp(); }}
        impl Drop for demo::Token {{ fn drop(&mut self) {{ owns self.n; ensures self.n == 9u32; }} by {{ execute(); simp(); }} }}
        fn demo::consume_token(token: demo::Token) -> u32 {{ ensures result == old(token.n); }} by {{ execute(); simp(); }}
        fn demo::drop_argument(x: u32) -> u32 {{ ensures result == x; }} by {{ execute(); simp(); }}
    "#
    );
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("result == x", "result != x"),
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

#[test]
#[ignore = "nightly: 15s in the parallel gate"]
fn rust_crate_scalar_constants_execute_checked_initializers() {
    let p = Project::new("");
    let source = r#"
        pub mod left { pub const MOD: u32 = 65521; pub fn read() -> u32 { MOD } }
        pub mod right { pub const MOD: u32 = 7; pub fn read() -> u32 { MOD } }
        pub fn entry() -> usize { const CHUNK_SIZE: usize = 5552 * 4; CHUNK_SIZE }
        pub fn wide() -> usize { const LIMIT: usize = 4294967296; LIMIT }
        pub fn small() -> u8 { const N: u8 = 5 * 4; N }
        pub fn flag() -> bool { const FLAG: bool = true; FLAG }
    "#;
    fs::write(p.root.join("lib.rs"), source).unwrap();
    fs::write(p.config(), serde_json::to_vec(&serde_json::json!({
        "schema":4,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"lib.rs",
        "exporter":std::env::var("CLICK_CHARON").unwrap(),"artifact":"crate.ullbc",
        "crate":{"name":"demo","edition":"2021","features":[],
            "roots":["demo::left::read","demo::right::read","demo::entry","demo::wide","demo::small","demo::flag"],"files":["lib.rs"]}
    })).unwrap()).unwrap();
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    let mut proof = String::from("verifying \"lib.rs\";\n");
    for function in &prepared.export().functions {
        let (ty, value) = if function.name.contains("_I4_left_") {
            ("u32", "65521u32")
        } else if function.name.contains("_I5_right_") {
            ("u32", "7u32")
        } else if function.name.contains("_I5_entry") {
            ("usize", "22208u64")
        } else if function.name.contains("_I4_wide") {
            ("usize", "4294967296u64")
        } else if function.name.contains("_I5_small") {
            ("u8", "20u8")
        } else if function.name.contains("_I4_flag") {
            ("bool", "1")
        } else {
            panic!("unexpected imported function {}", function.name);
        };
        proof.push_str(&format!(
            "fn {}() -> {ty} {{ ensures result == {value}; }} by {{ execute(); simp(); }}\n",
            click::surface::rust_display_name(&function.name).unwrap()
        ));
    }
    assert_eq!(prepared.export().functions.len(), 12);
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &proof.replace("result == 22208u64", "result == 22209u64"),
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
    // A failure names the item by its path, as the sidecar writes it.
    fs::write(
        p.root.join("borrow.click"),
        proof.replace("result == 22208u64", "result == 22209u64"),
    )
    .unwrap();
    let cli = p.cli(&["verify"]);
    let stderr = String::from_utf8_lossy(&cli.stderr);
    assert!(!cli.status.success());
    assert!(stderr.contains("demo::entry"), "{stderr}");
    assert!(!stderr.contains("__rust_q"), "{stderr}");
    let traced = p.cli(&["verify", "--trace-proof", "demo::entry::CHUNK_SIZE"]);
    let stderr = String::from_utf8_lossy(&traced.stderr);
    assert!(
        !traced.status.success(),
        "{stderr}{}",
        String::from_utf8_lossy(&traced.stdout)
    );
    assert!(!stderr.contains("not a selected proof"), "{stderr}");
    assert!(stderr.contains("demo::entry"), "{stderr}");
    // Lock loading checks the initializer's source too.
    fs::write(
        p.root.join("lib.rs"),
        source.replace("5552 * 4", "5553 * 4"),
    )
    .unwrap();
    assert!(p.prepared().is_err());
}
