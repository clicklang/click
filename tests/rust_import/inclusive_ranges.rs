use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/inclusive-ranges/inclusive.click");

/// A `for` over `start..=end` holds the range's bounds and whether it has
/// yielded `end`: it yields `end` once and stops, even at the type's maximum,
/// and verifies from ordinary invariants over `iter_start`, `iter_end` and
/// `iter_done`.
#[test]
fn charon_inclusive_range_loops_yield_their_end_once() {
    let p = Project::from_fixture("design/charon-trial/inclusive-ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    // `0u8..=255` yields every byte once, 255 included: 256 values, not 255.
    let function = SIDECAR
        .split("\nfn ")
        .find(|function| function.starts_with("every_byte"))
        .unwrap();
    let invalid = format!(
        "verifying \"inclusive.rs\";\nfn {}",
        function.replacen("result == 256u32;", "result == 255u32;", 1)
    );
    let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
        .err()
        .expect("`every_byte` claiming 255 iterations must fail");
    let rendered = format!("{error:?} {error}");
    assert!(rendered.contains("every_byte"), "{rendered}");
}
