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
        ("pub fn bad(x: u32) -> u32 { x }", "unsupported Rust type"),
        (
            "pub fn bad(mut x: i32) -> i32 { while x < 5 { x += 1; } x }",
            "supported typed Rust subset",
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
fn rust_owned_field_loan_recovery_fails_closed() {
    // Preserve the ordinary Rust source that exposed fragmented ownership at
    // the outer destructor call. Do not alter it to make the proof pass.
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(error.contains("field-loan recovery"), "{error}");
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        source
    );
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
