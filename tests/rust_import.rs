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
        fs::write(root.join("borrow.click.import.json"), serde_json::to_vec(&serde_json::json!({"schema":1,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"borrow.rs","exporter":exporter,"artifact":"borrow.rs.click-rust.json"})).unwrap()).unwrap();
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
