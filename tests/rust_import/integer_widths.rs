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

fn check_remainder_guards(ty: &str, maximum: &str, controls: bool) {
    let p = Project::from_fixture("design/charon-trial/narrow-remainder");
    fs::write(p.root.join("borrow.click"), "verifying \"widths.rs\";").unwrap();
    let prepared = p.prepared().unwrap();
    for (name, result, ensures) in [
        (
            format!("parity_{ty}"),
            format!(" -> {ty}"),
            format!("result == 1{ty}"),
        ),
        (format!("even_{ty}"), String::new(), "true".into()),
    ] {
        // Keep the original branch reproduction in the gate; the assertion
        // and mutation controls run together in the named nightly checks.
        if !controls && name.starts_with("even_") {
            continue;
        }
        let claim = format!(
            "verifying \"widths.rs\"; fn {name}(x: {ty}){result} {{ requires x % 2{ty} == 0{ty}; ensures {ensures}; }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared)
            .unwrap_or_else(|error| panic!("{claim}: {error:?}"));
        if controls {
            let invalid = claim.replace(&format!("requires x % 2{ty} == 0{ty};"), "");
            assert!(
                C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
                "{invalid}"
            );
        }
    }
    if !controls {
        return;
    }
    let odd = format!(
        "verifying \"widths.rs\"; fn parity_{ty}(x: {ty}) -> {ty} {{ requires x == {maximum}{ty}; ensures result == 0{ty}; }}"
    );
    C0VerificationSession::new_program_prepared(&odd, &prepared).unwrap();
}

#[test]
fn charon_u8_remainder_guards_match_contracts() {
    check_remainder_guards("u8", "255", false);
}

#[test]
fn charon_u16_remainder_guards_match_contracts() {
    check_remainder_guards("u16", "65535", false);
}

#[test]
#[ignore = "nightly: remainder boundary and missing-premise controls take 0.75s"]
fn charon_u32_remainder_guards_keep_unsigned_semantics() {
    check_remainder_guards("u32", "4294967295", true);
}

#[test]
#[ignore = "nightly: variable-divisor and zero-divisor controls take 0.86s"]
fn charon_narrow_remainder_keeps_variable_divisor_and_zero_checks() {
    let p = Project::from_fixture("design/charon-trial/narrow-remainder");
    fs::write(p.root.join("borrow.click"), "verifying \"widths.rs\";").unwrap();
    let prepared = p.prepared().unwrap();
    for ty in ["u8", "u16"] {
        let claim = format!(
            "verifying \"widths.rs\"; fn remainder_{ty}(x: {ty}, y: {ty}) -> {ty} {{ requires y != 0{ty}; ensures result == x % y; }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
        let invalid = format!(
            "verifying \"widths.rs\"; fn remainder_{ty}(x: {ty}, y: {ty}) -> {ty} {{ ensures true; }}"
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a possible zero divisor must be refused");
        assert!(error.to_string().contains("zero"), "{error:?}");
    }
}

#[test]
#[ignore = "nightly: narrow remainder boundary and missing-premise controls take 1.9s"]
fn charon_narrow_remainder_guards_reject_missing_premises_and_keep_boundaries() {
    check_remainder_guards("u8", "255", true);
    check_remainder_guards("u16", "65535", true);
}
