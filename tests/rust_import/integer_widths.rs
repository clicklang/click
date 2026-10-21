use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/integer-widths/widths.click");

/// `i8`, `i16`, `i64`, `isize` and `u64` parameters, results, locals,
/// references, struct and enum fields, `Option` payloads and `match`
/// scrutinees import at their widths and verify; each arithmetic step that
/// could overflow owes Rust's panic check.
#[test]
fn charon_integer_widths_verify_with_their_panic_checks() {
    let p = Project::from_fixture("design/charon-trial/integer-widths");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // `u64` addition checks the full unsigned width, as `usize` does.
        (
            "    requires a <= 1000u64 and b <= 1000u64;\n",
            "",
            "Rust add panic check",
        ),
        // `i8` subtraction is computed in `int`, which cannot overflow; the
        // panic check is the `i8` range.
        (
            "    requires 0i8 <= x and x <= 100i8 and 0i8 <= y and y <= 100i8;\n",
            "",
            "Rust sub panic check",
        ),
        // `i64` multiplication overflows the kernel's signed 64-bit word.
        (
            "    requires -1000i64 <= x and x <= 1000i64;\n",
            "",
            "signed overflow",
        ),
        // A compound assignment through `&mut i16` checks the `i16` range.
        ("    requires *x < 100i16;\n", "", "Rust add panic check"),
        // A widening cast keeps the value.
        (
            "fn widen16(x: i16) -> i64 {\n    ensures result == x as i64;",
            "fn widen16(x: i16) -> i64 {\n    ensures result == 0i64;",
            "widen16",
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

/// A whole-record `owns *account` seeds the record at its fields' widths,
/// so the fixture's `deposit` reads its `i64` and `u64` fields as one cell
/// each; a claim that the untouched field changes is refused.
#[test]
fn charon_whole_record_owns_covers_a_64_bit_field_load() {
    let p = Project::from_fixture("design/charon-trial/integer-widths");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    assert!(SIDECAR.contains("    owns *account;\n"));
    let before = "    ensures account.id == old(account.id);";
    assert!(SIDECAR.contains(before));
    let changed = SIDECAR.replacen(
        before,
        "    ensures account.id == old(account.id) + 1u64;",
        1,
    );
    let error = C0VerificationSession::new_program_prepared(&changed, &prepared)
        .err()
        .expect("a changed untouched field must be refused");
    assert!(format!("{error:?}").contains("deposit"), "{error:?}");
}
