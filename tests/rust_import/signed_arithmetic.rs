use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/signed-arithmetic/signed.click");

/// Signed division, remainder, negation and bitwise operations import and
/// verify; each owes Rust's panic checks: a nonzero divisor, no `MIN / -1`
/// or `MIN % -1`, and no negation of `MIN`.
#[test]
fn charon_signed_arithmetic_verifies_with_its_panic_checks() {
    let p = Project::from_fixture("design/charon-trial/signed-arithmetic");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // `i64` remainder by a possible zero.
        (
            "    requires 0i64 <= x and 0i64 < y;\n",
            "    requires 0i64 <= x;\n",
            "division by zero",
        ),
        // `i8` and `i16` are computed in `int`, where `MIN / -1` fits, so
        // they owe an explicit check.
        (
            "    requires 0i8 <= x and 0i8 < y;\n",
            "    requires y == -1i8;\n",
            "Rust div panic check",
        ),
        (
            "    requires 0i16 <= x and 0i16 < y;\n",
            "    requires y == -1i16;\n",
            "Rust rem panic check",
        ),
        // Negation is a subtraction from zero, with its checks.
        (
            "    requires -100i16 <= x and x <= 100i16;\n",
            "",
            "Rust sub panic check",
        ),
        ("    requires x != -2147483648i32;\n", "", "signed overflow"),
        // `isize` division through a reference: `MIN / -1` overflows the
        // kernel's signed 64-bit word.
        (
            "    requires 0isize <= *total and 0isize < parts;\n",
            "    requires parts != 0isize;\n",
            "signed overflow",
        ),
        // A bitwise result is the operation it lowers from.
        (
            "    ensures result == (x & y);\n",
            "    ensures result == (x | y);\n",
            "mask",
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
