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
    ] {
        assert_ne!(invalid, proof, "negative proof must change the sidecar");
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    // A growing measure is false even when the checker can derive the
    // remaining count's decrease without its explicit `have`. Its back-edge
    // diagnostic must spell the count through the iteration's mark.
    let growing = proof.replace(
        "decreases iter_remaining;",
        "decreases bytes.len() - iter_remaining;",
    );
    assert_ne!(growing, proof, "negative proof must change the sidecar");
    {
        let error = C0VerificationSession::new_program_prepared(&growing, &prepared)
            .err()
            .expect("a growing loop measure must be rejected")
            .to_string();
        assert!(!error.contains("budget exhausted"), "{error}");
        assert!(
            error.contains("bytes.len() - (at(iteration, iter_remaining) - 1u64) < bytes.len() - at(iteration, iter_remaining)"),
            "{error}"
        );
        assert!(!error.contains("<unnamed"), "{error}");
        assert!(error.contains("decreases at the back edge"), "{error}");
        assert!(!error.contains("__rust_"), "{error}");
        // The reference fixture names the loaded scalar explicitly; its
        // Rust local `byte` is a pointer, not the value added to `total`.
        let scalar_byte = if fixture == "rust-iter-references" {
            "loaded_byte"
        } else {
            "byte"
        };
        assert!(error.contains(&format!(" + {scalar_byte})")), "{error}");
        assert!(error.contains("prefix(old(bytes), bytes.len(),"), "{error}");
    }
}
#[cfg(not(feature = "fast-gate"))]
fn profile_agrees(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["profile"]);
}
#[cfg(not(feature = "fast-gate"))]
fn expansion_rechecks(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
#[cfg(not(feature = "fast-gate"))]
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
        #[cfg(not(feature = "fast-gate"))]
        fn $profile() {
            profile_agrees($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        #[cfg(not(feature = "fast-gate"))]
        fn $expand() {
            expansion_rechecks($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        #[cfg(not(feature = "fast-gate"))]
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
