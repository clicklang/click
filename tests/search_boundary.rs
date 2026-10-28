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
        "fn check(c: C) { c.diagnostic_fact_sample(12, 0); }",
        "fn check(c: C) { let f = C::diagnostic_fact_sample; f(c); }",
        "fn check(c: C) { invoke!(c.r#diagnostic_fact_sample()); }",
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
        // surface::planning and diagnostic_fact_sample are comments, not code.
        fn check(c: C) {
            let surface = 1;
            let message = "diagnostic_fact_sample";
            c.get(&surface);
            c.scan_explicit_input();
        }
        #[cfg(test)] mod tests { use crate::surface::planning::proposition_search::PropositionSearch; }
    "#;
    assert!(boundary::check_source("src/kernel/checker.rs", source).is_ok());
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

#[test]
fn selected_reasoning_requires_explicit_premises_or_planner_permission() {
    let temp = tempfile::tempdir().unwrap();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let permission = root.join("src/surface/planning/permission.rs");
    let selected = root.join("src/kernel/assumptions/selected_facts.rs");
    for (body, succeeds) in [
        ("let _ = SelectedFacts::from_propositions(&[1, 2]);", true),
        (
            "let _ = SelectedFacts { context: std::borrow::Cow::Owned(PureFactContext::new()) };",
            false,
        ),
        (
            "let _ = SelectedFacts::for_search(&PureFactContext::new(), SearchPermission::new());",
            false,
        ),
        (
            "let _: SelectedFacts = PureFactContext::new().into();",
            false,
        ),
        (
            "let mut facts = SelectedFacts::from_propositions(&[]); *facts = PureFactContext::new();",
            false,
        ),
    ] {
        // Compile the actual constructor module, with a minimal fact store.
        // No cfg(test): production must not gain the test-only adapter.
        let source = format!(
            r#"
            #![allow(dead_code, unused_imports)]
            mod planning {{
                #[path = {permission:?}] mod permission;
                pub(crate) use permission::SearchPermission;
                pub(crate) fn search() {{
                    let _ = crate::kernel::SelectedFacts::for_search(
                        &crate::kernel::PureFactContext::new(), SearchPermission::new());
                }}
            }}
            use planning::SearchPermission;
            mod kernel {{
                pub(crate) type Proposition = u8;
                #[derive(Clone)] pub(crate) struct PureFactContext;
                impl PureFactContext {{
                    pub(crate) fn new() -> Self {{ Self }}
                    fn assume_proposition(self, _: Proposition) -> Self {{ self }}
                }}
                pub(crate) fn clone_proposition_iteratively(p: &Proposition) -> Proposition {{ *p }}
                #[path = {selected:?}] mod selected_facts;
                pub(crate) use selected_facts::SelectedFacts;
            }}
            mod checking {{
                use crate::{{kernel::{{SelectedFacts, PureFactContext}}, SearchPermission}};
                fn check() {{ {body} }}
            }}
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
            "{body}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn fact_withdrawal_is_only_available_in_tests() {
    for path in ["src/kernel/checker.rs", "src/surface/planning/search.rs"] {
        for source in [
            "fn check(c: C, p: P) { c.without_exact_fact(&p); }",
            "fn check() { let f = C::remove_proposition_fact; }",
            "fn check() { hidden!(c.forget_condition_fact(p)); }",
            "impl C { fn without_exact_fact(&self) {} }",
        ] {
            assert!(
                boundary::check_source(path, source).is_err(),
                "accepted {source}"
            );
        }
        assert!(
            boundary::check_source(
                path,
                "impl C { #[cfg(test)] fn without_exact_fact(&self) {} }"
            )
            .is_ok()
        );
    }
}
