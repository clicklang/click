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
        // A shift's count is below the operand's width: 8 for `i8`, not
        // the 32 C allows for its promoted word.
        (
            "    requires n < 8u32;\n",
            "    requires n < 9u32;\n",
            "Rust shl panic check",
        ),
        // A negative count is as out of range as a large one.
        (
            "    requires 0i32 <= n and n < 64i32;\n",
            "    requires n < 64i32;\n",
            "Rust shr panic check",
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
        // A panic check's refusal states its condition over the source
        // locals, never the lowering's checked temporaries.
        if expected.ends_with("panic check") {
            let message = error.to_string();
            assert!(message.contains("could not show `"), "{message}");
            assert!(!message.contains("__rust_"), "{message}");
        }
    }
}

#[test]
fn rust_shift_resource_arguments_retain_width_and_count_obligations() {
    let p = Project::from_fixture("design/charon-trial/signed-arithmetic");
    let source = SIDECAR
        .replace("fn shift_left(x: i32, n: u32) -> i32 {", "abstract resource word(value: i32);\nfn shift_left(x: i32, n: u32) -> i32 {\n    owns word(-1i32 << 1u32);")
        .replace("fn shift_narrow(x: i8, n: u32) -> i8 {", "abstract resource byte(value: i8);\nfn shift_narrow(x: i8, n: u32) -> i8 {\n    owns byte(x << n);")
        .replace("    owns *total;", "    owns total[0..(1i32 << 0u32)];");
    fs::write(p.root.join("borrow.click"), &source).unwrap();
    let prepared = p.prepared().unwrap();
    // A UInt32 endpoint is independently unsupported by the existing range
    // representation, even without a shift. Keep that failure separate from
    // the Rust count domain this regression exercises.
    let literal_control = source.replace("total[0..(1i32 << 0u32)]", "total[0..1u32]");
    let literal_error = C0VerificationSession::new_program_prepared(&literal_control, &prepared)
        .err()
        .unwrap_or_else(|| panic!("the direct UInt32 index control unexpectedly verified"));
    assert!(
        literal_error.to_string().contains("integer index"),
        "{literal_error}"
    );
    C0VerificationSession::new_program_prepared(&source, &prepared)
        .unwrap_or_else(|error| panic!("Rust shifts in resource arguments and bounds: {error:?}"));
    let narrow_extent = source.replace(
        "total[0..(1i32 << 0u32)]",
        "total[0..((1i8 << 0u32) as i32)]",
    );
    C0VerificationSession::new_program_prepared(&narrow_extent, &prepared)
        .unwrap_or_else(|error| panic!("a valid narrow shift, widened to an index: {error:?}"));
    for invalid in [
        source.replace("owns byte(x << n);", "owns byte(x << 8u32);"),
        narrow_extent.replace("1i8 << 0u32", "1i8 << 8u32"),
    ] {
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("an invalid narrow Rust shift count must be rejected"));
        let message = error.to_string();
        assert!(
            !message.contains("integer index"),
            "the count obligation, rather than an unsupported index type, must fail: {message}"
        );
    }
}
