//! Frozen sources and sidecars distinguish normalization from proof-interface parity.
use super::*;

fn project(name: &str, positive: bool) -> Project {
    let p = Project::from_fixture("design/charon-trial/loop-headers");
    let sidecar = match (name, positive) {
        ("loops", true) => "loops-proof.click",
        ("loops", false) => "loops.click",
        ("sum", true) => "sum-proof.click",
        ("sum", false) => "sum.click",
        ("headers", _) => "headers.click",
        _ => panic!("unknown checkpoint"),
    };
    fs::copy(p.root.join(sidecar), p.root.join("borrow.click")).unwrap();
    p
}

#[test]
fn charon_loop_headers_import_unchanged_fixtures_and_retain_frontier_gaps() {
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/loops.rs"),
        include_str!("../../examples/rust-loops/loops.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/loops-assignments.click"),
        include_str!("../../examples/rust-loops/loops.click")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/sum.rs"),
        include_str!("../../examples/rust-byte-sum/sum.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/loop-headers/sum-proof.click"),
        include_str!("../../examples/rust-byte-sum/sum.click")
    );
    for (name, diagnostic) in [
        ("loops", "requires the execution frontier to be at a loop"),
        ("sum", "local `i` has no value at this frontier"),
    ] {
        let p = project(name, false);
        let prepared = p.prepared().unwrap();
        let error = C0VerificationSession::new_program_prepared(
            &super::parity::frozen_proof_input(
                &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            ),
            &prepared,
        )
        .err()
        .expect("retain the numeric-frontier proof-interface gap");
        assert!(error.message().contains(diagnostic), "{error:?}");
    }
}

/// A loop phase of a Rust function is expanded by its label over the
/// prepared program, through the program entry point and through the
/// input-generic one `click expand --claim` uses: the omitted phase becomes
/// an explicit proof in the `loop` tactic, and the rewrite checks.
#[test]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn charon_loop_phase_expands_by_label_over_the_prepared_program() {
    let p = project("loops", true);
    let prepared = p.prepared().unwrap();
    let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let inputs = click::surface::ProgramInputs::program(&prepared);
    for phase in ["initialize", "preserve"] {
        let label = format!("count.loop(0).{phase}");
        let expanded = click::surface::expand_program_prepared_claim_source_by_label(
            &sidecar, &prepared, &label,
        )
        .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        // The written-out preservation cites a `click::machine_integer`
        // theorem, so expansion adds that import ahead of the otherwise
        // unchanged sidecar; the initialization cites none.
        let import = match phase {
            "initialize" => "",
            _ => "import click::machine_integer;\n",
        };
        let body = expanded
            .strip_prefix(import)
            .unwrap_or_else(|| panic!("{label}: expansion adds `{import}`\n{expanded}"));
        let insertion = sidecar.find("}\n    execute(); simp();").unwrap();
        assert!(body.starts_with(&sidecar[..insertion]), "{expanded}");
        assert!(body.ends_with(&sidecar[insertion..]), "{expanded}");
        assert!(
            body[insertion..].starts_with(&format!("    {phase} by {{\n")),
            "{expanded}"
        );
        let generic = click::surface::expand_claim_by_label(None, &sidecar, &inputs, &label, None)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        assert_eq!(generic.source, expanded, "{label}");
        assert_eq!(generic.proof_unit, "count.contract", "{label}");
        C0VerificationSession::new_program_prepared(&expanded, &prepared)
            .unwrap_or_else(|error| panic!("{label}: {}\n{expanded}", error.message()));
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_loop_headers_check_real_guards_final_assignments_and_false_claims() {
    for name in ["loops", "sum", "headers"] {
        let p = project(name, true);
        let prepared = p.prepared().unwrap();
        let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
        for (before, after) in [
            ("ensures result == n;", "ensures result == 0;"),
            ("ensures result == bytes.len();", "ensures result == 0u64;"),
            (
                "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes.len()));",
                "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes.len())) + 1;",
            ),
        ] {
            let invalid = sidecar.replace(before, after);
            if invalid != sidecar {
                assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
            }
        }
    }
}

#[test]
#[ignore = "nightly: 15 s, over the gate's per-test budget (2026-10-06)"]
fn charon_loop_headers_tools_recheck_expanded_certificates() {
    for (name, claims) in [
        (
            "loops",
            &["count.contract", "accumulate.contract", "walk.contract"][..],
        ),
        ("sum", &["sum.contract"][..]),
        (
            "headers",
            &["final_header.contract", "negated.contract"][..],
        ),
    ] {
        let p = project(name, true);
        for command in ["profile", "audit"] {
            assert_cli(&p, &[command]);
        }
        for claim in claims {
            assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        }
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_loop_headers_live_refresh_and_effectful_header_rejections() {
    for name in ["loops", "sum", "headers"] {
        let p = project(name, true);
        p.refresh().unwrap();
        let prepared = p.prepared().unwrap();
        C0VerificationSession::new_program_prepared(
            &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            &prepared,
        )
        .unwrap();
        if name == "loops" {
            let original = fs::read_to_string(p.root.join("loops.rs")).unwrap();
            // Add an unrelated compiler local without editing the frozen fixture.
            fs::write(
                p.root.join("loops.rs"),
                original.replacen("let mut i = 0;", "let unrelated = n; let mut i = 0;", 1),
            )
            .unwrap();
            p.refresh().unwrap();
            let prepared = p.prepared().unwrap();
            let sidecar = assignment_frontier_sidecar();
            C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
            fs::write(p.root.join("loops.rs"), original).unwrap();
            p.refresh().unwrap();
        }
        if name == "sum" {
            let original = fs::read_to_string(p.root.join("sum.rs")).unwrap();
            fs::write(
                p.root.join("sum.rs"),
                original.replacen(
                    "let mut total = 0i32;",
                    "let unrelated = bytes.len(); let mut total = 0i32;",
                    1,
                ),
            )
            .unwrap();
            p.refresh().unwrap();
            let prepared = p.prepared().unwrap();
            C0VerificationSession::new_program_prepared(
                &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
                &prepared,
            )
            .unwrap();
        }
        if name != "headers" {
            continue;
        }
        for (source, diagnostic) in [
            (
                "pub fn bad(value: &i32) { while *value > 0 {} }",
                "pure scalar copies",
            ),
            (
                "pub fn guard(n: i32)->bool { n > 0 } pub fn bad(n: i32) { while guard(n) {} }",
                "conditional while header",
            ),
            (
                "pub fn bad(n: i32) { let mut i=0; while i<n+1 { i+=1; } }",
                "pure scalar copies",
            ),
            (
                "pub fn bad(n: i32) { let mut i=0; while i<n { if i==2 { break; } i+=1; } }",
                "extra exit",
            ),
        ] {
            fs::remove_file(p.artifact("headers.rs")).unwrap();
            fs::write(p.root.join("headers.rs"), source).unwrap();
            let error = p.refresh().unwrap_err();
            assert!(error.contains(diagnostic), "{error}");
            assert!(!p.artifact("headers.rs").exists());
            fs::write(
                p.root.join("headers.rs"),
                include_str!("../../design/charon-trial/loop-headers/headers.rs"),
            )
            .unwrap();
            p.refresh().unwrap();
        }
    }
}

fn assignment_frontier_sidecar() -> &'static str {
    include_str!("../../design/charon-trial/loop-headers/loops-assignments.click")
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_assignment_frontiers_select_source_locals_and_recheck_tools() {
    let p = project("loops", true);
    let sidecar = assignment_frontier_sidecar();
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for (from, to) in [
        ("assignment(i, 0)", "assignment(absent, 0)"),
        ("have i == 0", "have i == 1"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar.replace(from, to), &prepared)
                .is_err()
        );
    }
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in ["count.contract", "accumulate.contract", "walk.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}
