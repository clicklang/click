use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/scalar-slices/slices.click");

/// Shared and mutable slices of any integer element import as a pointer and
/// a length: indexed reads and writes owe Rust's index panic check, and a
/// slice passes to a callee whole.
#[test]
fn charon_scalar_slices_verify_with_their_index_checks() {
    let p = Project::from_fixture("design/charon-trial/scalar-slices");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // A write past the end of a `&mut [i64]`.
        (
            "    owns *xs;\n    requires k < xs.len();\n    ensures xs[k] == v;",
            "    owns *xs;\n    ensures xs[k] == v;",
            "Rust slice index panic check",
        ),
        // A read past the end of a `&[u16]`.
        (
            "    views *xs;\n    requires k < xs.len();\n    ensures result == xs[k];",
            "    views *xs;\n    ensures result == xs[k];",
            "Rust slice index panic check",
        ),
        // The swap moves the last element to the front, not the first.
        (
            "    ensures xs.len() >= 2 implies xs[0] == old(xs[xs.len() - 1]);",
            "    ensures xs.len() >= 2 implies xs[0] == old(xs[0]);",
            "swap_ends",
        ),
    ] {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}
