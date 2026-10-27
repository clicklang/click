#[path = "../build_support/search_boundary.rs"]
#[allow(dead_code)]
mod boundary;

#[test]
fn checking_rejects_planner_dependencies_and_enumeration_escape_hatches() {
    for source in [
        "use crate::surface::planning::proposition_search::PropositionSearch;",
        "use crate::{surface as s};",
        "fn check() { crate::surface::hidden!(); }",
        "fn check() { include!(\"hidden.rs\"); }",
        "fn check() { crate::surface::planning::search(); }",
        "fn check(c: C) { c.scan_for_legacy_simp(); }",
        "fn check(c: C) { c.diagnostic_proposition_facts(); }",
        "fn check(c: C) { let f = C::scan_for_legacy_simp; f(c); }",
        "fn check(c: C) { invoke!(c.r#scan_for_legacy_simp()); }",
        "macro_rules! hidden { () => { crate::surface::planning::search() } }",
    ] {
        assert!(
            boundary::check_source("src/kernel/new_checker.rs", source).is_err(),
            "accepted {source}"
        );
    }
}

#[test]
fn checking_accepts_indexed_and_explicit_input_work_and_test_dependencies() {
    let source = r#"
        // surface::planning and scan_for_legacy_simp are comments, not code.
        fn check(c: C) {
            let surface = 1;
            let message = "scan_for_legacy_simp";
            c.get(&surface);
            c.scan_explicit_input();
        }
        #[cfg(test)] mod tests { use crate::surface::planning::proposition_search::PropositionSearch; }
    "#;
    assert!(boundary::check_source("src/kernel/checker.rs", source).is_ok());
}

#[test]
fn a_reviewed_legacy_function_cannot_add_another_scan() {
    let path = "src/kernel/assumptions/condition_reasoning/simp.rs";
    let once = "fn bitvector_terms_equal_for_simp(c: C) { c.scan_for_legacy_simp(); }";
    let twice = "fn bitvector_terms_equal_for_simp(c: C) { c.scan_for_legacy_simp(); c.scan_for_legacy_simp(); }";
    assert!(boundary::check_source(path, once).is_ok());
    assert!(boundary::check_source(path, twice).is_err());
}

#[test]
fn module_walk_checks_production_files_even_when_named_tests() {
    let temp = tempfile::tempdir().unwrap();
    let kernel = temp.path().join("src/kernel");
    std::fs::create_dir_all(&kernel).unwrap();
    std::fs::write(kernel.join("mod.rs"), "mod innocent_tests;").unwrap();
    std::fs::write(kernel.join("innocent_tests.rs"), "use crate::surface as s;").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_err());
    std::fs::write(kernel.join("mod.rs"), "#[cfg(test)] mod innocent_tests;").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_ok());
}

#[test]
fn only_planning_can_construct_search_permission() {
    let temp = tempfile::tempdir().unwrap();
    let permission =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/surface/planning/permission.rs");
    for (body, succeeds) in [
        (
            "pub(crate) fn check(_: &crate::planning::SearchPermission) {}",
            true,
        ),
        (
            "fn check() { let _ = crate::planning::SearchPermission::new(); }",
            false,
        ),
        (
            "fn check() { let _ = crate::planning::SearchPermission { _private: () }; }",
            false,
        ),
    ] {
        let source = format!(
            r#"
            #![allow(dead_code)]
            mod planning {{
                #[path = {permission:?}] mod permission;
                pub(crate) use permission::SearchPermission;
                pub(crate) fn search() {{ let permission = SearchPermission::new(); consume(&permission); }}
                fn consume(_: &SearchPermission) {{}}
            }}
            mod checking {{ {body} }}
        "#
        );
        let file = temp.path().join("probe.rs");
        std::fs::write(&file, source).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["--edition=2024", "--crate-type=lib", "--emit=metadata"])
            .arg(&file)
            .arg("--out-dir")
            .arg(temp.path())
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            succeeds,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if !succeeds {
            assert!(String::from_utf8_lossy(&output.stderr).contains("private"));
        }
    }
}
