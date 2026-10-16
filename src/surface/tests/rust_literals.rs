use super::*;

fn prove(body: &str) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    verify_c0_sources(
        &format!("verifying \"literals.rs\"; {body}"),
        &[("literals.rs", "")],
    )
}

#[test]
fn rust_integer_literals_preserve_native_types_and_signed_boundaries() {
    for (ty, min, max) in [
        ("i8", "128", "127"),
        ("i16", "32768", "32767"),
        ("i32", "2147483648", "2147483647"),
        ("i64", "9223372036854775808", "9223372036854775807"),
        ("isize", "9223372036854775808", "9223372036854775807"),
    ] {
        prove(&format!(
            "theorem limits() {{
            ensures -{min}{ty} < 0{ty} by {{ normalize(); }}
            ensures {max}{ty} > 0{ty} by {{ normalize(); }}
            ensures -(({min}{ty})) == -{min}{ty} by {{ normalize(); }}
        }}"
        ))
        .unwrap_or_else(|error| panic!("{ty}: {error:?}"));
    }
    for (ty, max) in [
        ("u8", "255"),
        ("u16", "65535"),
        ("u32", "4294967295"),
        ("u64", "18446744073709551615"),
        ("usize", "18446744073709551615"),
    ] {
        prove(&format!(
            "theorem limits() {{ ensures {max}{ty} > 0{ty} by {{ normalize(); }} }}"
        ))
        .unwrap_or_else(|error| panic!("{ty}: {error:?}"));
    }
    // In particular, explicit i64 must retain its type even at the i32 boundary.
    prove("function large() -> i64 { -2147483648i64 }
           theorem width() { ensures large() == -2147483648i64 by { unfold(large()); normalize(); } }")
        .unwrap();
}

#[test]
fn rust_integer_radices_and_separators_verify() {
    prove(
        r#"theorem spelling_boundaries() {
        ensures 0xff_ff_u16 == 65535u16 by { normalize(); }
        ensures 0b__1__u32 == 1u32 by { normalize(); }
        ensures 0o7_7u8 == 63u8 by { normalize(); }
        ensures -0x8000_0000i32 < 0i32 by { normalize(); }
        ensures -(0x8000_0000_0000_0000isize) < 0isize by { normalize(); }
    }
    theorem mathematical(value: Integer) {
        requires value == 0x1_0000_0000_0000_0000;
        ensures value == 18_446_744_073_709_551_616 by { assumption(); }
    }"#,
    )
    .unwrap();
    assert!(
        prove("theorem false_claim() { ensures 0xffu8 == 254u8 by { normalize(); } }").is_err()
    );
    assert!(
        prove("theorem false_claim() { ensures 0x1_0000 == 0u16 by { normalize(); } }").is_err()
    );
}

#[test]
fn rust_integer_literals_reject_overflow_and_invalid_spellings() {
    for (literal, message) in [
        ("128i8", "out of range for `i8`"),
        ("-129i8", "out of range for `i8`"),
        ("32768i16", "out of range for `i16`"),
        ("-32769i16", "out of range for `i16`"),
        ("2147483648i32", "out of range for `i32`"),
        ("-(2147483648i32 + 0i32)", "out of range for `i32`"),
        ("-2147483649i32", "out of range for `i32`"),
        ("9_223_372_036_854_775_808i64", "out of range for `i64`"),
        ("-9_223_372_036_854_775_809i64", "out of range for `i64`"),
        ("9223372036854775808isize", "out of range for `isize`"),
        ("-9223372036854775809isize", "out of range for `isize`"),
        ("256_u8", "out of range for `u8`"),
        ("65536u16", "out of range for `u16`"),
        ("0x1_0000_0000u32", "out of range for `u32`"),
        ("0x1_0000_0000_0000_0000u64", "out of range for `u64`"),
        ("18446744073709551616usize", "out of range for `usize`"),
        ("-1usize", "cannot negate a `usize`"),
        ("-1u32", "cannot negate a `u32`"),
        ("0b102u8", "invalid base-2"),
        ("0o89u16", "invalid base-8"),
        ("0x_u32", "invalid base-16"),
        ("1u128", "unsupported integer literal suffix `u128`"),
        ("1i128", "unsupported integer literal suffix `i128`"),
        ("1f32", "unsupported integer literal suffix `f32`"),
        ("1u16oops", "unsupported integer literal suffix `u16oops`"),
    ] {
        let source = format!(
            "verifying \"literals.rs\"; theorem bad() {{ ensures {literal} == {literal}; }}"
        );
        let error = parser::parse(&source).expect_err(literal);
        assert!(error.message().contains(message), "{literal}: {error:?}");
    }
}

#[test]
fn rust_integer_literal_syntax_does_not_change_c_or_cpp_sidecars() {
    for language in ["c", "cpp"] {
        for literal in ["65_535", "0xff", "0b10", "0o77", "1u16", "1usize", "1i32"] {
            let source = format!(
                "verifying \"source.{language}\"; theorem bad() {{ ensures {literal} == {literal}; }}"
            );
            let error = parser::parse(&source).unwrap_err();
            assert!(
                error.message().contains("requires a Rust sidecar"),
                "{error:?}"
            );
        }
    }
    verify_c0_sources(
        "verifying \"source.c\"; theorem legacy() {
        ensures 255u8 > 0u8 by { normalize(); }
        ensures 4294967295u32 > 0u32 by { normalize(); }
        ensures -9223372036854775808i64 < 0i64 by { normalize(); }
        ensures 18446744073709551615u64 > 0u64 by { normalize(); }
    }",
        &[("source.c", "")],
    )
    .unwrap();
}
