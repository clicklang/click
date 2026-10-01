use click::languages::rust::{load_import, refresh_import};
use click::surface::C0VerificationSession;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

const SOURCE: &str = include_str!("../examples/basic-rust/borrow.rs");
const SIDECAR: &str = include_str!("../examples/basic-rust/borrow.click");
struct Project {
    root: PathBuf,
}
impl Project {
    fn new(source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "click-rust-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let exporter = std::env::var("CLICK_RUST_EXPORTER")
            .expect("build-rust-exporter.sh supplies CLICK_RUST_EXPORTER");
        fs::write(root.join("borrow.rs"), source).unwrap();
        fs::write(root.join("borrow.click"), SIDECAR).unwrap();
        fs::write(root.join("borrow.click.import.json"), serde_json::to_vec(&serde_json::json!({"schema":2,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"borrow.rs","exporter":exporter,"artifact":"borrow.rs.click-rust.json"})).unwrap()).unwrap();
        Self { root }
    }
    fn config(&self) -> PathBuf {
        self.root.join("borrow.click.import.json")
    }
    fn cli(&self, args: &[&str]) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .arg(self.root.join("borrow.click"))
            .output()
            .unwrap()
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
#[test]
fn rust_typed_import_verifies_borrow_parent_reuse_and_field_frame() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    assert_eq!(verified.len(), 12);
    let false_claim = SIDECAR.replace("ensures result == 8;", "ensures result == 9;");
    assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
}
#[test]
fn rust_lock_rejects_changed_source_and_artifact() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    fs::write(p.root.join("borrow.rs"), format!("{SOURCE}\n// changed")).unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    fs::write(p.root.join("borrow.rs"), SOURCE).unwrap();
    fs::write(p.root.join("borrow.rs.click-rust.json"), b"{}").unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
}
#[test]
fn rust_compiler_and_subset_rejections_are_distinct() {
    for (source, diagnostic) in [
        (
            "pub fn bad(p: &mut i32) { let child = &mut *p; *p = 4; *child = 7; }",
            "cannot assign",
        ),
        ("pub fn bad(x: u64) -> u64 { x }", "unsupported Rust type"),
        (
            "pub fn bad(mut x: i32) -> i32 { loop { x += 1; } }",
            "unlabeled Rust while",
        ),
        (
            "mod other; pub fn ok(x:i32)->i32{x}",
            "Rust source boundary",
        ),
        (
            "pub fn ok(x:i32)->i32 { include!(\"other.rs\") }",
            "Rust source boundary",
        ),
        ("pub unsafe fn bad(x:i32)->i32{x}", "unsafe or generic"),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
        assert!(!p.root.join("borrow.rs.click-rust.json").exists());
    }
}
fn assert_cli(p: &Project, args: &[&str]) {
    let result = p.cli(args);
    assert!(
        result.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&result.stderr)
    );
}
#[test]
fn rust_ordinary_cli_locks_and_verifies() {
    let p = Project::new(SOURCE);
    assert_cli(&p, &["import", "lock"]);
    assert_cli(&p, &["verify"]);
}
#[test]
fn rust_cli_profile_and_audit_use_the_shared_engine() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
}
#[test]
fn rust_cli_expansion_reverifies_through_ordinary_entry() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "update.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_checked_arithmetic_requires_a_panic_freedom_bound() {
    let p = Project::new("pub fn increment(x:i32)->i32 { x + 1 }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; int32 increment(int32 x) { ensures result == x + 1; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(claim, &prepared).is_err());
    let bounded = claim.replace("ensures result", "requires x < 2147483647; ensures result");
    C0VerificationSession::new_program_prepared(&bounded, &prepared).unwrap();
}

#[test]
fn rust_boolean_return_and_local_initialization_verify() {
    let p = Project::new("pub fn invert(x:bool)->bool { let answer = !x; answer }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; bool invert(bool x) { ensures result == (if x != 0 { 0 } else { 1 }); } by { if x == 0 { execute(); simp(); } else { execute(); simp(); } }";
    C0VerificationSession::new_program_prepared(claim, &prepared).unwrap();
}

const MOVE_SOURCE: &str = include_str!("../examples/rust-move-drop/guard.rs");
const MOVE_SIDECAR: &str = include_str!("../examples/rust-move-drop/guard.click");
fn moves_project(source: &str) -> (Project, String) {
    let p = Project::new(source);
    let sidecar = MOVE_SIDECAR.replace("guard.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    (p, sidecar)
}
#[test]
fn rust_moves_drop_effect_and_return_capture_verify() {
    let (p, sidecar) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for wrong in [
        sidecar.replace(
            "ensures value[0] == old(value[0]);",
            "ensures value[0] == 7;",
        ),
        sidecar.replace(
            "ensures self->slot[0] == old(self->saved);",
            "ensures self->slot[0] == 7;",
        ),
        sidecar.replace(
            "ensures result == (if early != 0 { 7 } else { 9 });",
            "ensures result == old(value[0]);",
        ),
        sidecar[sidecar.find("int32 restore").unwrap()..]
            .to_string()
            .replace("int32 restore", "verifying \"borrow.rs\"; int32 restore"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&wrong, &prepared).is_err());
    }
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        MOVE_SOURCE
    );
}
#[test]
fn rust_move_borrow_conflicts_and_partial_moves_fail_closed() {
    for (source, diagnostic) in [
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let b=a; a.x}",
            "use of moved value",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let r=&a;let b=a;r.x}",
            "cannot move out",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad(a:S)->i32 {a.x}",
            "Rust value type",
        ),
        (
            "pub struct S<'a> {pub p:&'a mut i32} pub fn bad(p:&mut i32) {let a=S{p};let moved=a.p;*moved=4;}",
            "partial moves",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config())
            .and_then(|_| {
                let prepared = load_import(&p.config())?;
                C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
                    .map(|_| ())
                    .map_err(|e| format!("{e:?}"))
            })
            .unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
    }
}
#[test]
fn rust_move_drop_cli_proofs_expand_and_reverify() {
    let (p, _) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "restore.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

fn replace_artifact(p: &Project, export: &click::languages::rust::schema::RustExport) {
    use sha2::{Digest, Sha256};
    let bytes = serde_json::to_vec(export).unwrap();
    fs::write(p.root.join("borrow.rs.click-rust.json"), &bytes).unwrap();
    let lock_path = p.root.join("borrow.click.import.json.lock");
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(&lock_path).unwrap()).unwrap();
    lock["artifact"] = format!("{:x}", Sha256::digest(&bytes)).into();
    let identity = format!(
        "click-rust-import-v2\n{}\n{}\n{}\n{}\n{}\n{}",
        lock["config"].as_str().unwrap(),
        lock["source"].as_str().unwrap(),
        lock["exporter"].as_str().unwrap(),
        lock["artifact"].as_str().unwrap(),
        click::languages::rust::schema::COMPILER_COMMIT,
        click::languages::rust::schema::TARGET
    );
    lock["identity"] = format!("{:x}", Sha256::digest(identity.as_bytes())).into();
    fs::write(lock_path, serde_json::to_vec(&lock).unwrap()).unwrap();
}
#[test]
fn rust_kernel_rejects_duplicate_move_drop_and_missing_cleanup() {
    use click::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    let (p, sidecar) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    let original = load_import(&p.config()).unwrap().export().clone();
    for corruption in 0..4 {
        let mut export = original.clone();
        let mir = export
            .functions
            .iter_mut()
            .find(|f| f.name == "restore")
            .unwrap()
            .mir
            .as_mut()
            .unwrap();
        if corruption == 0 || corruption == 3 {
            let statements = &mut mir.blocks[0].statements;
            let index = statements
                .iter()
                .position(|s| matches!(s, S::Move { .. }))
                .unwrap();
            let extra = if corruption == 0 {
                statements[index].clone()
            } else {
                let S::Move { source, record, .. } = &statements[index] else {
                    unreachable!()
                };
                S::Assign {
                    target: click::languages::rust::schema::Expression::Local {
                        name: "__rust_mir_0".into(),
                    },
                    value: click::languages::rust::schema::Expression::Field {
                        base: Box::new(click::languages::rust::schema::Expression::Local {
                            name: source.clone(),
                        }),
                        record: record.clone(),
                        field: "saved".into(),
                    },
                }
            };
            statements.insert(index + 1, extra);
        } else {
            let index = mir
                .blocks
                .iter()
                .position(|b| matches!(b.terminator, T::Drop { .. }))
                .unwrap();
            let T::Drop {
                local,
                record,
                target,
            } = mir.blocks[index].terminator.clone()
            else {
                unreachable!()
            };
            if corruption == 1 {
                let duplicate = mir.blocks.len();
                mir.blocks.push(click::languages::rust::schema::MirBlock {
                    statements: vec![],
                    terminator: T::Drop {
                        local: local.clone(),
                        record: record.clone(),
                        target,
                    },
                });
                mir.blocks[index].terminator = T::Drop {
                    local,
                    record,
                    target: duplicate,
                };
            } else {
                mir.blocks[index].terminator = T::Goto { target };
            }
        }
        replace_artifact(&p, &export);
        let prepared = load_import(&p.config()).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "corruption {corruption}"
        );
    }
}
#[test]
fn rust_conditional_move_and_explicit_drop_verify() {
    let source = format!(
        "{}    if early {{ let moved = guard; *moved.slot = 7; std::mem::drop(moved); 7 }}\n    else {{ *guard.slot = 9; 9 }}\n}}\n",
        MOVE_SOURCE.split("    let moved = guard;").next().unwrap()
    );
    let (p, sidecar) = moves_project(&source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
fn rust_owned_field_loan_recovery_verifies() {
    // Preserve the ordinary Rust source that exposed fragmented ownership at
    // the outer destructor call. Do not alter it to make the proof pass.
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* value) {{ owns value[0..1]; ensures value[0] == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("value[0] == 42", "value[0] == 1"),
            &prepared
        )
        .is_err()
    );
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        source
    );
}

#[test]
fn rust_owned_field_loan_cli_expands_and_reverifies() {
    let p = Project::new(include_str!("../examples/rust-field-borrow/guard.rs"));
    fs::write(
        p.root.join("borrow.click"),
        include_str!("../examples/rust-field-borrow/guard.click").replace("guard.rs", "borrow.rs"),
    )
    .unwrap();
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "cleanup.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_owned_field_parent_can_write_after_explicit_child_drop() {
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; std::mem::drop(second); first.saved = 43; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* value) {{ owns value[0..1]; ensures value[0] == 43; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
fn rust_owned_disjoint_mutable_fields_verify() {
    let source = "pub struct Pair {pub x:i32,pub y:i32} pub fn set(left:&mut i32,right:&mut i32) {*left=7;*right=9;} pub fn fields()->i32 {let mut pair=Pair{x:1,y:2}; let left=&mut pair.x; let right=&mut pair.y; set(left,right); if pair.y == 9 {pair.x} else {0}}";
    let p = Project::new(source);
    let sidecar = "verifying \"borrow.rs\"; void set(int32* left,int32* right) {owns left[0..1];owns right[0..1];ensures left[0]==7;ensures right[0]==9;} by {execute();simp();} int32 fields() {ensures result==7;} by {execute();simp();}";
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result==7", "result==0"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_owned_field_conflicting_parent_access_is_rejected_by_compiler() {
    let prefix = MOVE_SOURCE.split("pub fn restore").next().unwrap();
    for (suffix, diagnostic) in [
        ("first.saved=5; std::mem::drop(second);", "cannot assign"),
        (
            "std::mem::drop(first); std::mem::drop(second);",
            "cannot move out",
        ),
        (
            "std::mem::drop(second); *second.slot=5;",
            "use of moved value",
        ),
    ] {
        let source = format!(
            "{prefix}pub fn bad(value:&mut i32) {{ let mut first=Guard{{slot:value,saved:1}}; let second=Guard{{slot:&mut first.saved,saved:42}}; {suffix} }}"
        );
        let p = Project::new(&source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert_eq!(
            fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
            source
        );
    }
}

#[test]
fn rust_moves_plain_struct_and_reads_destination() {
    let p =
        Project::new("pub struct S {pub x:i32} pub fn plain()->i32 {let a=S{x:17}; let b=a; b.x}");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        "verifying \"borrow.rs\"; int32 plain() {ensures result == 17;} by {execute(); simp();}",
        &prepared,
    )
    .unwrap();
}

#[test]
fn rust_two_guards_clean_up_in_reverse_construction_order() {
    use click::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    let source = format!(
        "{}pub fn cleanup(left:&mut i32,right:&mut i32) {{ let first=Guard{{slot:left,saved:17}}; let second=Guard{{slot:right,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}void cleanup(int32* left,int32* right) {{ owns left[0..1]; owns right[0..1]; ensures left[0] == 17; ensures right[0] == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("int32 restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let mir = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name == "cleanup")
        .unwrap()
        .mir
        .as_ref()
        .unwrap();
    let constructors = mir
        .blocks
        .iter()
        .flat_map(|b| &b.statements)
        .filter_map(|s| match s {
            S::Initialize { target, .. } => Some(target.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut drops = Vec::new();
    let mut block = 0;
    loop {
        match &mir.blocks[block].terminator {
            T::Drop { local, target, .. } => {
                drops.push(local.clone());
                block = *target;
            }
            T::Goto { target } => block = *target,
            T::Return => break,
            _ => panic!("unexpected cleanup edge"),
        }
    }
    assert_eq!(drops, constructors.into_iter().rev().collect::<Vec<_>>());
}

const UNSIGNED_SOURCE: &str = include_str!("../examples/rust-unsigned/arithmetic.rs");
const UNSIGNED_SIDECAR: &str = include_str!("../examples/rust-unsigned/arithmetic.click");

#[test]
fn rust_unsigned_arithmetic_and_expansion_verify() {
    let p = Project::new(UNSIGNED_SOURCE);
    let sidecar = UNSIGNED_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 9);
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 0;", "ensures result == 1;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add_byte.contract",
        "shifted_byte.contract",
        "low_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_unsigned_panic_paths_are_rejected() {
    for (ty, expression, precondition) in [
        ("u32", "x + 1", "x == 4294967295u32"),
        ("u8", "x + 1", "x == 255"),
        ("u32", "x - 1", "x == 0"),
        ("u8", "x - 1", "x == 0"),
        ("u32", "x * 2", "x == 4294967295u32"),
        ("u8", "x * 2", "x == 255"),
        ("u32", "1 / x", "x == 0"),
        ("u8", "1 % x", "x == 0"),
        ("u32", "1 << x", "x == 32"),
        ("u8", "1 >> x", "x == 8"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:{ty})->{ty} {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let cty = if ty == "u8" { "uint8" } else { "uint32" };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {cty} bad({cty} x) {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
fn rust_unsigned_nested_checks_and_short_circuit_preserve_panics() {
    for (expression, return_type, valid) in [
        ("(x + 1) as u8", "uint8", false),
        ("false && x + 1 > 0", "bool", true),
        ("true || x + 1 > 0", "bool", true),
        ("true && x + 1 > 0", "bool", false),
        ("false || x + 1 > 0", "bool", false),
    ] {
        let rust_type = if return_type == "bool" { "bool" } else { "u8" };
        let p = Project::new(&format!(
            "pub fn check(x:u32)->{rust_type} {{ {expression} }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {return_type} check(uint32 x) {{ requires x == 4294967295u32; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{expression}: {:?}", result.err());
    }
}

#[test]
fn rust_unsigned_casts_bitwise_and_assignments_verify() {
    let p = Project::new(
        "pub fn bits(mut x:u8)->u8 { x ^= 255; x &= 254; x |= 1; !x } pub fn narrow(x:i32)->u8 { x as u8 } pub fn signed(x:u32)->i32 { x as i32 } pub fn shift(x:u32, n:i32)->u32 { x >> n } pub fn byte_count(x:u32, n:u8)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint8 bits(uint8 x) { requires x == 128; ensures result == 128; } by { execute(); simp(); }
uint8 narrow(int32 x) { requires x == -1; ensures result == 255; } by { execute(); simp(); }
int32 signed(uint32 x) { requires x == 4294967295u32; ensures result == -1; } by { execute(); simp(); }
uint32 shift(uint32 x, int32 n) { requires x == 4294967295u32; requires n == 31; ensures result == 1u32; } by { execute(); simp(); }
uint32 byte_count(uint32 x, uint8 n) { requires n < 32u32; ensures result == (x << (uint32)n); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("n == 31", "n == -1"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_unsigned_references_and_byte_field_layout_verify() {
    let p = Project::new(
        "pub struct Pair { pub byte:u8, pub word:u32 } pub fn write(p:&mut u8, q:&mut u32) { *p = 255; *q = 4294967295; } pub fn field(p:&mut Pair) { p.byte = 7; }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
void write(uint8* p, uint32* q) { owns p[0..1]; owns q[0..1]; ensures p[0] == 255; ensures q[0] == 4294967295u32; } by { execute(); simp(); }
void field(struct Pair* p) { owns p->byte; owns p->word; ensures p->byte == 7; ensures p->word == old(p->word); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const SLICES_SOURCE: &str = include_str!("../examples/rust-slices/bytes.rs");
const SLICES_SIDECAR: &str = include_str!("../examples/rust-slices/bytes.click");

#[test]
fn rust_byte_slices_indexing_calls_and_expansion_verify() {
    let p = Project::new(SLICES_SOURCE);
    let sidecar = SLICES_SIDECAR.replace("bytes.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    for claim in ["read.contract", "write.contract", "length.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_byte_slices_variable_length_indexing_verify() {
    let p = Project::new("pub fn read(bytes:&[u8], index:usize)->u8 { bytes[index] }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint8 read(const uint8* bytes, uint64 bytes_len, uint64 index) {
    requires bytes_len <= 2147483647u64;
    requires index < bytes_len;
    views bytes[0..(int32)bytes_len];
    ensures result == bytes[(int32)index];
} by { execute(); simp(); }";
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "read.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_byte_slices_reject_panics_and_missing_write_authority() {
    for (source, signature, resource, index) in [
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            0u64,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            4,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "uint8 bad(const uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            4294967296,
        ),
        (
            "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] = 7; }",
            "void bad(uint8* bytes, uint64 bytes_len, uint64 index)",
            "views",
            1,
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let length = if index == 0 { 0 } else { 4 };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ requires bytes_len == {length}u64; requires index == {index}u64; {resource} bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("unsafe slice contract must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        if resource == "views" && signature.starts_with("void") {
            assert!(error.message().contains("owns"), "{}", error.message());
        } else {
            assert!(
                error.message().contains("Rust slice index panic check"),
                "{}",
                error.message()
            );
        }
    }
}

#[test]
fn rust_byte_slices_length_preserves_target_width_and_index_borrows_verify() {
    let p = Project::new(
        "pub fn length(bytes:&[u8])->usize { bytes.len() } pub fn replace(bytes:&mut [u8], index:usize) { let child = &mut bytes[index]; *child = 9; } pub fn shift(x:u32, n:usize)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
uint64 length(const uint8* bytes, uint64 bytes_len) { requires bytes_len == 4294967296u64; ensures result == 4294967296u64; } by { execute(); simp(); }
void replace(uint8* bytes, uint64 bytes_len, uint64 index) { requires bytes_len == 4u64; requires index < 4u64; owns bytes[0..4]; ensures bytes[(int32)index] == 9; } by { execute(); simp(); }
uint32 shift(uint32 x, uint64 n) { requires x == 1u32; requires n == 31u64; ensures result == 2147483648u32; } by { execute(); rewrite(n == 31u64); rewrite(x == 1u32); normalize(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let error = C0VerificationSession::new_program_prepared(
        &sidecar.replace("n == 31u64", "n == 4294967296u64"),
        &prepared,
    )
    .err()
    .expect("oversized usize shift must fail before truncation");
    assert!(
        error.message().contains("Rust shl panic check"),
        "{}",
        error.message()
    );
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 4294967296u64", "ensures result == 0u64"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_byte_slice_unsupported_shapes_and_borrow_errors_are_refused() {
    for (source, message) in [
        (
            "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] += 1; }",
            "indexed compound assignments",
        ),
        (
            "pub fn bad(bytes:&[u8])->&[u8] { bytes }",
            "returns are not supported",
        ),
        (
            "pub fn bad(bytes:&[u32])->usize { bytes.len() }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes:&mut [u8]) { let child = &mut *bytes; bytes[0] = 1; child[0] = 2; }",
            "cannot",
        ),
    ] {
        let p = Project::new(source);
        let result = refresh_import(&p.config());
        assert!(result.unwrap_err().contains(message), "{source}");
    }
}

#[test]
fn rust_fixed_array_references_indexing_and_reborrows_verify() {
    let p = Project::new(include_str!("../examples/rust-arrays/arrays.rs"));
    let sidecar =
        include_str!("../examples/rust-arrays/arrays.click").replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "read.contract",
        "write.contract",
        "signed.contract",
        "first.contract",
        "update.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures words[1] == 7u32", "ensures words[1] == 8u32"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_fixed_array_indices_reject_panics_before_narrowing() {
    for (length, index) in [(4, 4u64), (4, 4294967296), (0, 0), (4, u64::MAX)] {
        let p = Project::new(&format!(
            "pub fn read(bytes: &[u8; {length}], index: usize) -> u8 {{ bytes[index] }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint8 read(const uint8* bytes, uint64 index) {{ requires index == {index}u64; views bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array index must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust array index panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_fixed_array_access_requires_memory_authority() {
    for (source, signature, resources) in [
        (
            "pub fn read(bytes: &[u8; 4]) -> u8 { bytes[0] }",
            "uint8 read(const uint8* bytes)",
            "",
        ),
        (
            "pub fn write(words: &mut [u32; 3]) { words[1] = 7; }",
            "void write(uint32* words)",
            "views words[0..3];",
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {resources} ensures 1 == 1; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array access requires authority");
        assert_eq!(
            error.kind(),
            click::surface::ClickErrorKind::Proof,
            "{}",
            error.message()
        );
        assert!(
            error.message().contains(if resources.is_empty() {
                "views"
            } else {
                "owns"
            }),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_fixed_array_unsupported_shapes_and_conflicting_borrows_are_refused() {
    for (source, message) in [
        (
            "pub fn bad(bytes: &[u64; 4]) -> u64 { bytes[0] }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(words: &[u32; 536870912]) -> usize { words.len() }",
            "storage exceeds",
        ),
        (
            "pub fn bad(bytes: [u8; 4]) -> u8 { bytes[0] }",
            "by-value Rust arrays",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { bytes[0] += 1; }",
            "indexed compound assignments",
        ),
        (
            "pub fn bad(bytes: &[u8; 4]) -> &[u8] { bytes }",
            "reference/aggregate returns",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let child = &mut bytes[0]; bytes[0] = 1; *child = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(message), "expected {message}: {error}");
        assert!(!p.root.join("borrow.rs.click-rust.json").exists());
    }
}

#[test]
fn rust_local_array_construction_and_whole_value_copies_verify() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "literal.contract",
        "independent.contract",
        "replace.contract",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 8;", "ensures result == 16;"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_whole_array_copies_require_authority_for_every_element() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for unsupported in [
        sidecar.replace("views source[0..2];", "views source[0..1];"),
        sidecar.replace("owns target[0..2];", "views target[0..2];"),
        sidecar.replace("owns target[0..2];", "owns target[0..1];"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&unsupported, &prepared).is_err(),
            "unexpectedly verified: {unsupported}"
        );
    }
}

#[test]
fn rust_arrays_coerce_to_byte_slices_with_lengths_and_authority() {
    let p = Project::new(include_str!("../examples/rust-array-slices/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-slices/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "local.contract",
        "alias.contract",
        "retarget_mut.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    for incorrect in [
        sidecar.replace("ensures result == 4u64;", "ensures result == 1u64;"),
        sidecar.replace(
            "uint8 read(const uint8* bytes) {\n    views bytes[0..1];",
            "uint8 read(const uint8* bytes) {",
        ),
        sidecar.replace(
            "uint8 mutate(uint8* bytes) {\n    owns bytes[1..2];",
            "uint8 mutate(uint8* bytes) {\n    views bytes[1..2];",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&incorrect, &prepared).is_err());
    }
    let overflow = Project::new(
        &include_str!("../examples/rust-array-slices/arrays.rs")
            .replace("[3u8, 5, 9]", "[255u8, 5, 9]"),
    );
    refresh_import(&overflow.config()).unwrap();
    let overflow_prepared = load_import(&overflow.config()).unwrap();
    let error = C0VerificationSession::new_program_prepared(&sidecar, &overflow_prepared)
        .err()
        .expect("overflow must be rejected");
    assert!(
        error.message().contains("Rust add panic check"),
        "{}",
        error.message()
    );
}

#[test]
fn rust_array_to_slice_coercions_preserve_bounds_and_borrow_checks() {
    for (source, diagnostic) in [
        (
            "pub fn bad(bytes: &[u8; 4]) { let s: &mut [u8] = bytes; s[0] = 1; }",
            "mismatched types",
        ),
        (
            "pub fn bad(words: &[u32; 4]) -> usize { let s: &[u32] = words; s.len() }",
            "unsupported Rust type",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let s: &mut [u8] = bytes; bytes[0] = 1; s[0] = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
    let p = Project::new(
        "pub fn read(bytes: &[u8; 2], index: usize) -> u8 { let s: &[u8] = bytes; s[index] }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for index in ["2u64", "4294967296u64", "18446744073709551615u64"] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint8 read(const uint8* bytes, uint64 index) {{ requires index == {index}; views bytes[0..2]; ensures result == 0; }} by {{ execute(); simp(); }}"
        );
        assert!(C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err());
    }
}

#[test]
fn rust_local_array_authority_and_copies_scale_with_array_length() {
    let mut samples = Vec::new();
    for length in [4, 16, 64] {
        let p = Project::new(&format!(
            "pub fn first(bytes: &[u8]) -> u8 {{ bytes[0] }} pub fn run() -> u8 {{ let bytes = [7u8; {length}]; let copied = bytes; first(&copied) }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = "verifying \"borrow.rs\"; uint8 first(const uint8* bytes, uint64 bytes_len) { requires bytes_len > 0u64; requires bytes_len <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } uint8 run() { ensures result == 7; } by { execute(); simp(); }";
        let (result, work) = click::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(sidecar, &prepared)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 8,
            "array verification grew faster than its explicit operations: {samples:?}"
        );
    }
}

#[test]
fn rust_array_to_slice_calls_preserve_untouched_local_elements() {
    let p = Project::new(
        "pub fn first(bytes: &[u8]) -> u8 { bytes[0] } pub fn set(bytes: &mut [u8]) { bytes[1] = 7; } pub fn untouched() -> u8 { let mut bytes = [3u8, 5, 9]; set(&mut bytes); bytes[0] } pub fn initial() -> u8 { let bytes = [3u8, 5, 9]; first(&bytes) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; uint8 first(const uint8* bytes, uint64 bytes_len) { requires bytes_len > 0u64; requires bytes_len <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } void set(uint8* bytes, uint64 bytes_len) { requires bytes_len > 1u64; requires bytes_len <= 2147483647u64; owns bytes[1..2]; ensures bytes[1] == 7; } by { execute(); simp(); } uint8 untouched() { ensures result == 3; } by { execute(); simp(); } uint8 initial() { ensures result == 3; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const USIZE_SOURCE: &str = include_str!("../examples/rust-usize/arithmetic.rs");
const USIZE_SIDECAR: &str = include_str!("../examples/rust-usize/arithmetic.click");

#[test]
fn rust_usize_arithmetic_casts_and_expansion_verify() {
    let p = Project::new(USIZE_SOURCE);
    let sidecar = USIZE_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let general_mul = sidecar.replace(
        "requires x == 4294967296u64;\n    requires y == 2147483648u64;\n    ensures result == 9223372036854775808u64;",
        "requires y != 0u64;\n    requires x <= 18446744073709551615u64 / y;\n    ensures result == x * y;",
    );
    assert_ne!(general_mul, sidecar);
    C0VerificationSession::new_program_prepared(&general_mul, &prepared).unwrap();
    for changed in [
        sidecar.replace("requires index == 0u64;", "requires index == 1u64;"),
        sidecar.replace(
            "requires index == 0u64;",
            "requires index == 18446744073709551615u64;",
        ),
        sidecar.replace(
            "requires bytes_len <= 18446744073709551614u64;",
            "requires bytes_len == 18446744073709551615u64;",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&changed, &prepared).is_err());
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace(
                "ensures result == 9223372036854775808u64;",
                "ensures result == 0u64;"
            ),
            &prepared,
        )
        .is_err()
    );
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add.contract",
        "mul.contract",
        "right.contract",
        "computed.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_usize_panic_paths_are_rejected() {
    for (expression, precondition) in [
        ("x + 1", "x == 18446744073709551615u64"),
        ("x - 1", "x == 0u64"),
        ("x * 2", "x == 9223372036854775808u64"),
        ("1 / x", "x == 0u64"),
        ("1 % x", "x == 0u64"),
        ("1 << x", "x == 64u64"),
        ("1 >> x", "x == 4294967296u64"),
        ("1 << x", "x == 18446744073709551615u64"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:usize)->usize {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; uint64 bad(uint64 x) {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
fn rust_usize_boundaries_and_nested_checks() {
    for (source, return_type, precondition, expected, valid) in [
        (
            "x + 0",
            "uint64",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x * 0",
            "uint64",
            "x == 18446744073709551615u64",
            "0u64",
            true,
        ),
        (
            "x * 1",
            "uint64",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x - 1",
            "uint64",
            "x == 9223372036854775808u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x / 2",
            "uint64",
            "x == 18446744073709551615u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x % 2",
            "uint64",
            "x == 18446744073709551615u64",
            "1u64",
            true,
        ),
        (
            "{ let mut y = x; y += 1; y -= 1; y *= 1; y /= 1; y %= 2; y <<= 63; y >>= 63; y }",
            "uint64",
            "x == 4294967297u64",
            "1u64",
            true,
        ),
        (
            "(x + 1) as u32",
            "uint32",
            "x == 18446744073709551615u64",
            "0u32",
            false,
        ),
        (
            "false && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "0",
            true,
        ),
        (
            "true || x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            true,
        ),
        (
            "true && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            false,
        ),
    ] {
        let ty = match return_type {
            "uint32" => "u32",
            "bool" => "bool",
            _ => "usize",
        };
        let p = Project::new(&format!("pub fn check(x:usize)->{ty} {{ {source} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {return_type} check(uint64 x) {{ requires {precondition}; ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{source}: {:?}", result.err());
    }
    let p = Project::new("pub fn right(x:usize, n:i32)->usize { x >> n }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; uint64 right(uint64 x, int32 n) { requires n == -1; ensures result == result; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(sidecar, &prepared).is_err());
}

#[test]
fn rust_while_loop_invariants_verify_and_expand() {
    let p = Project::new(include_str!("../examples/rust-loops/loops.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-loops/loops.click").replace("loops.rs", "borrow.rs");
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 3);
    for false_claim in [
        sidecar.replace("ensures result == n;", "ensures result == n + 1;"),
        sidecar.replace("invariant i <= bytes_len;", "invariant i < bytes_len;"),
        sidecar.replace("decreases bytes_len - i;", "decreases i;"),
        sidecar.replace("requires value == 1;", "requires value == 2147483647;"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in ["count.contract", "accumulate.contract", "walk.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn rust_while_loop_rejects_unsupported_control_flow_and_guards() {
    for (source, diagnostic) in [
        ("pub fn bad() { for _i in 0..2 {} }", "Rust for loops"),
        (
            "pub fn bad() { 'outer: while true {} }",
            "unlabeled Rust while",
        ),
        (
            "pub fn bad() { while true { break; } }",
            "break and continue",
        ),
        (
            "pub fn bad() { while true { continue; } }",
            "break and continue",
        ),
        (
            "pub fn bad(mut i:i32, n:i32) { while i + 1 < n { i += 1; } }",
            "Rust while conditions",
        ),
        (
            "fn guard()->bool { false } pub fn bad() { while guard() {} }",
            "Rust while conditions",
        ),
        (
            "pub fn bad(bytes:&[u8]) { while bytes[0] != 0 {} }",
            "Rust while conditions",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
}

#[test]
fn rust_while_loop_panic_paths_are_rejected() {
    for (source, signature, invariant) in [
        (
            "pub fn bad(mut i:i32) { while i >= 0 { i += 1; } }",
            "void bad(int32 i)",
            "i >= 0",
        ),
        (
            "pub fn bad(mut i:usize) { while i <= 18446744073709551615usize { i += 1; } }",
            "void bad(uint64 i)",
            "i <= 18446744073709551615u64",
        ),
        (
            "pub fn bad(bytes:&[u8]) { let mut i=0usize; while i <= bytes.len() { let _byte=bytes[i]; i += 1; } }",
            "void bad(const uint8* bytes, uint64 bytes_len)",
            "i <= bytes_len",
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let prefix = if signature.contains("bytes") {
            "execute_until(statement(4));"
        } else {
            "step();"
        };
        let requirements = if signature.contains("bytes") {
            "requires bytes_len <= 2147483647u64; views bytes[0..(int32)bytes_len];"
        } else {
            "step();"
        };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {requirements} }} by {{ {prefix} loop {{ invariant {invariant}; }} execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("panic path must be rejected");
        assert!(
            !error.message().contains("requires the execution frontier"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_nested_while_loop_invariants_keep_preorder_indices() {
    let p = Project::new(
        "pub fn nested()->i32 { let mut i=0; while i < 1 { let mut j=0; while j < 1 { j += 1; } i += 1; } i }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; int32 nested() { ensures result == 1; } by { execute_until(statement(4)); loop { decreases 1-i; invariant 0<=i and i<=1; preserve by { execute_until(statement(9)); loop { decreases 1-j; invariant 0<=j and j<=1; } execute_until(statement(24)); step(); close_invariants(); } } execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["expand", "--claim", "nested.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_readable_local_names_preserve_shadowed_binding_identities() {
    let p = Project::new(
        "pub fn run(n:i32)->i32 { let n=2; let n=n+1; let __rust_checked_0=n+1; __rust_checked_0 }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; int32 run(int32 n) { ensures result == 4; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result == 4", "result == 3"),
            &prepared
        )
        .is_err()
    );
}

#[test]
fn rust_byte_sum_proves_exact_prefix_sum_and_expands() {
    let p = Project::new(include_str!("../examples/rust-byte-sum/sum.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-byte-sum/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace("invariant i <= bytes_len;", "invariant i < bytes_len;"),
        sidecar.replace(
            "invariant to_integer(total) == prefix(bytes, (int32)(uint32)i);",
            "invariant to_integer(total) + 1 == prefix(bytes, (int32)(uint32)i);",
        ),
        sidecar.replace("decreases bytes_len - i;", "decreases i;"),
        sidecar.replace("requires bytes_len <= 1000u64;", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_slice_for_sum_verifies_and_expands() {
    let p = Project::new(include_str!("../examples/rust-iterators/sum.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-iterators/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let copied_iter = Project::new(
        &include_str!("../examples/rust-iterators/sum.rs")
            .replace("in bytes {", "in bytes.iter() {"),
    );
    refresh_import(&copied_iter.config()).unwrap();
    let copied_prepared = load_import(&copied_iter.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &copied_prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace(
            "decreases bytes_len - __rust_iter_index_3_5;",
            "decreases __rust_iter_index_3_5;",
        ),
        sidecar.replace(
            "invariant __rust_iter_index_3_5 <= bytes_len;",
            "invariant __rust_iter_index_3_5 < bytes_len;",
        ),
        sidecar.replace("requires bytes_len <= 1000u64;", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
fn rust_slice_for_rejects_unsupported_iteration() {
    for source in [
        "pub fn bad(bytes: &[u8]) { for byte in bytes.iter().rev() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter_mut() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter() {} }",
        "pub fn bad(bytes: &[u8]) { let iter = bytes.iter(); for byte in iter {} }",
        "pub fn bad(mut bytes: &[u8]) { for byte in bytes.iter() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes {} }",
        "pub fn bad(mut bytes: &[u8]) { for &byte in bytes {} }",
        "pub fn bad(bytes: &[u8]) { 'outer: for &byte in bytes {} }",
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { break; } }",
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { continue; } }",
        "pub fn bad(bytes: &[u8; 2]) { for &byte in bytes {} }",
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(
            error.contains("Rust for loops")
                || error.contains("break and continue")
                || error.contains("unsupported Rust type `std::slice::Iter"),
            "{error}"
        );
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
fn rust_slice_iter_reference_sum_verifies_and_expands() {
    let source = include_str!("../examples/rust-iter-references/sum.rs");
    let sidecar =
        include_str!("../examples/rust-iter-references/sum.click").replace("sum.rs", "borrow.rs");
    // Shared references from both the implicit slice iterator and .iter()
    // have the same checked address and dereference semantics.
    for source in [source.to_string(), source.replace("bytes.iter()", "bytes")] {
        let p = Project::new(&source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
        for invalid in [
            sidecar.replace(
                "ensures to_integer(result) == old(prefix",
                "ensures to_integer(result) + 1 == old(prefix",
            ),
            sidecar.replace("requires bytes_len <= 1000u64;", ""),
            sidecar.replace("views bytes[0..(int32)(uint32)bytes_len];", ""),
            sidecar.replace(
                "decreases bytes_len - __rust_iter_index_3_5;",
                "decreases __rust_iter_index_3_5;",
            ),
        ] {
            assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
        }
        if source.contains(".iter()") {
            fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
            assert_cli(&p, &["profile"]);
            assert_cli(&p, &["audit"]);
            assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
            assert_cli(&p, &["verify"]);
        }
    }
    let p = Project::new("pub fn bad(bytes: &[u8]) { for byte in bytes.iter() { *byte = 0; } }");
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(error.contains("cannot assign"), "{error}");
}
