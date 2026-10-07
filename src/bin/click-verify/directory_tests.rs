//! Project-directory verdicts: `click verify <dir>` reconciles each sidecar's
//! `extern` declarations against the functions its sibling sidecars verify.
use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Directory(PathBuf);

impl Directory {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = env::temp_dir().join(format!(
            "click-directory-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        Self(fs::canonicalize(path).unwrap())
    }

    fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }

    fn verify(&self) -> Result<(), String> {
        entry_with([self.0.display().to_string()])
    }
}

impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const CALLER_C: &str = "int32 g(int32 x);\nint32 f(int32 x) { return g(x); }\n";
const CALLER_CLICK: &str = r#"verifying "a.c";
extern int32 g(int32 x) {
    ensures result == 42;
}
int32 f(int32 x) {
    ensures result == 42;
} by {
    execute();
    simp();
}
"#;

/// `callee.click` verifies `g` with the true contract `result == x`;
/// `caller.click` assumes `result == 42` for the same `g` and proves a false
/// claim about `f` from it. The directory verdict names the declaration and
/// both sidecars instead of verifying both.
#[test]
fn directory_refuses_an_extern_contract_for_a_function_a_sibling_sidecar_verifies() {
    let directory = Directory::new();
    directory.write("a.c", CALLER_C);
    directory.write("b.c", "int32 g(int32 x) { return x; }\n");
    directory.write(
        "callee.click",
        "verifying \"b.c\";\nint32 g(int32 x) {\n    ensures result == x by auto;\n}\n",
    );
    directory.write("caller.click", CALLER_CLICK);

    let error = directory.verify().unwrap_err();
    assert!(error.contains("`extern g`"), "{error}");
    assert!(error.contains("caller.click"), "{error}");
    assert!(error.contains("callee.click"), "{error}");
    assert!(error.contains("b.c"), "{error}");
}

/// `f` calls `g` and `g` calls `f`, each defined in its own sidecar and
/// assumed by the other. Neither returns, yet each sidecar alone verifies
/// `result == 42`; the directory refuses the cross-sidecar assumption rather
/// than reporting two verified sidecars.
#[test]
fn directory_refuses_sidecars_that_assume_each_others_contracts() {
    let directory = Directory::new();
    directory.write("a.c", CALLER_C);
    directory.write("a.click", CALLER_CLICK);
    directory.write(
        "b.c",
        "int32 f(int32 x);\nint32 g(int32 x) { return f(x); }\n",
    );
    directory.write(
        "b.click",
        r#"verifying "b.c";
extern int32 f(int32 x) {
    ensures result == 42;
}
int32 g(int32 x) {
    ensures result == 42;
} by {
    execute();
    simp();
}
"#,
    );

    let error = directory.verify().unwrap_err();
    // Sidecars are visited in sorted order, so `a.click`'s assumption is the
    // one reported; either direction would be refused.
    assert!(error.contains("`extern g`"), "{error}");
    assert!(error.contains("a.click"), "{error}");
    assert!(error.contains("b.click"), "{error}");
}

/// An `extern` declaration of a function no sidecar of the project defines
/// stays an ordinary external assumption, and sibling sidecars that define
/// unrelated functions do not disturb it.
#[test]
fn directory_keeps_genuinely_external_assumptions() {
    let directory = Directory::new();
    directory.write(
        "a.c",
        "int32 h(int32 x);\nint32 f(int32 x) { return h(x); }\n",
    );
    directory.write(
        "a.click",
        r#"verifying "a.c";
extern int32 h(int32 x) {
    ensures result == 42;
}
int32 f(int32 x) {
    ensures result == 42;
} by {
    execute();
    simp();
}
"#,
    );
    directory.write("b.c", "int32 g(int32 x) { return x; }\n");
    directory.write(
        "b.click",
        "verifying \"b.c\";\nint32 g(int32 x) {\n    ensures result == x by auto;\n}\n",
    );

    directory.verify().unwrap();
}

/// Two sidecars may verify one source each on their own; the rule is about
/// assuming, not about defining a function twice.
#[test]
fn directory_accepts_sidecars_that_verify_the_same_source() {
    let directory = Directory::new();
    directory.write("a.c", CALLER_C);
    directory.write("b.c", "int32 g(int32 x) { return 42; }\n");
    directory.write(
        "a.click",
        r#"verifying "a.c";
verifying "b.c" as callee;
int32 g(int32 x) {
    ensures result == 42 by auto;
}
int32 f(int32 x) {
    ensures result == 42;
} by {
    execute();
    simp();
}
"#,
    );
    directory.write(
        "b.click",
        "verifying \"b.c\";\nint32 g(int32 x) {\n    ensures result == 42 by auto;\n}\n",
    );

    directory.verify().unwrap();
}
