use super::*;

fn project(fixture: &str) -> Project {
    let p = Project::from_fixture(&format!("design/charon-trial/iterator-proof/{fixture}"));
    fs::copy(p.root.join("sum.click"), p.root.join("borrow.click")).unwrap();
    p
}
fn preserves_source_and_checks_obligations(fixture: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let migrated = root
        .join("design/charon-trial/iterator-proof")
        .join(fixture);
    let original = root.join("examples").join(fixture);
    assert_eq!(
        fs::read(migrated.join("sum.rs")).unwrap(),
        fs::read(original.join("sum.rs")).unwrap()
    );
    assert_eq!(
        fs::read(migrated.join("sum.click")).unwrap(),
        fs::read(original.join("sum.click")).unwrap()
    );
    let p = project(fixture);
    let prepared = p.prepared().unwrap();
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    assert!(!proof.contains("__rust_"));
    assert!(!proof.contains("statement("));
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for invalid in [
        proof.replacen("views bytes[0..bytes.len()];", "", 1),
        proof.replacen(
            "== old(prefix(bytes, bytes.len()));",
            "== old(prefix(bytes, bytes.len())) + 1;",
            1,
        ),
        // The remaining count is a `usize`; a measure that grows is refused.
        proof.replace(
            "decreases iter_remaining;",
            "decreases bytes.len() - iter_remaining;",
        ),
    ] {
        assert_ne!(invalid, proof, "negative proof must change the sidecar");
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    // The decrease left open at the back edge is spelled through the
    // iteration's mark: the `usize` remaining count it held there is a
    // pointer integer, and no recent statement snapshot holds it.
    if let Some(without) = without_statement(
        &proof,
        "have iter_remaining < at(iteration, iter_remaining)",
    ) {
        let error = C0VerificationSession::new_program_prepared(&without, &prepared)
            .err()
            .expect("the decrease is needed")
            .to_string();
        // The rejected candidates a trace lists are formatted by the steps
        // themselves; the report's own spelling comes before them.
        let report = error
            .lines()
            .take_while(|line| !line.contains("checked candidate"))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            report.contains("at(iteration, iter_remaining) - 1u64 < at(iteration, iter_remaining)"),
            "{error}"
        );
        assert!(!report.contains("<unnamed"), "{error}");
        assert!(!report.contains("__rust_"), "{error}");
        assert!(report.contains(" + byte)"), "{error}");
        assert!(
            report.contains("prefix(old(bytes), bytes.len(),"),
            "{error}"
        );
    }
}
/// `proof` without the statement whose first line starts with `prefix`: that
/// line when it ends the statement, otherwise through the `}` closing its
/// `by { ... }` block at the same indentation.
fn without_statement(proof: &str, prefix: &str) -> Option<String> {
    let lines = proof.lines().collect::<Vec<_>>();
    let start = lines
        .iter()
        .position(|line| line.trim_start().starts_with(prefix))?;
    let indent = &lines[start][..lines[start].len() - lines[start].trim_start().len()];
    let end = if lines[start].ends_with(';') {
        start
    } else {
        start
            + lines[start..]
                .iter()
                .position(|line| *line == format!("{indent}}}"))?
    };
    let mut kept = lines[..start].to_vec();
    kept.extend_from_slice(&lines[end + 1..]);
    Some(kept.join("\n"))
}
fn profile_agrees(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["profile"]);
}
fn expansion_rechecks(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
fn audits_checked_frontiers(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["verify"]);
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    for selector in [
        "execute_until(read(0))",
        "execute_until(assignment(total, 1))",
        "execute_until(back_edge())",
    ] {
        let offset = proof.find(selector).unwrap();
        let line = proof[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
        let column = offset - proof[..offset].rfind('\n').map_or(0, |p| p + 1) + 1;
        let cursor = format!("{}:{line}:{column}", p.root.join("borrow.click").display());
        assert_cli(&p, &["audit", "--start-at", &cursor, "--max-sites", "1"]);
        assert_eq!(
            fs::read_to_string(p.root.join("borrow.click")).unwrap(),
            proof,
            "audit must leave the original input unchanged"
        );
    }
}

macro_rules! iterator_checks {
    ($fixture:literal, $obligations:ident, $profile:ident, $expand:ident, $audit:ident) => {
        #[test]
        #[ignore = "nightly: 8s in the parallel gate"]
        fn $obligations() {
            preserves_source_and_checks_obligations($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $profile() {
            profile_agrees($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $expand() {
            expansion_rechecks($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $audit() {
            audits_checked_frontiers($fixture);
        }
    };
}
iterator_checks!(
    "rust-iterators",
    charon_iterator_proof_preserves_source_and_checks_obligations,
    charon_iterator_proof_profile_agrees,
    charon_iterator_proof_expansion_rechecks,
    charon_iterator_proof_audits_checked_frontiers
);
iterator_checks!(
    "rust-iter-references",
    charon_reference_iterator_proof_preserves_source_and_checks_obligations,
    charon_reference_iterator_proof_profile_agrees,
    charon_reference_iterator_proof_expansion_rechecks,
    charon_reference_iterator_proof_audits_checked_frontiers
);
