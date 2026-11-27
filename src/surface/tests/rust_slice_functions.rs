use super::*;

fn prove(body: &str) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    verify_c_sources(
        &format!("verifying \"slices.rs\"; {body}"),
        &[("slices.rs", "")],
    )
}

const SIZES: &str = "
    function size(bytes: &[u8]) -> usize { bytes.len() }
    function both(bytes: &[u8], bytes_len: usize) -> usize { size(bytes) + bytes_len }
";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn a_pure_function_slice_parameter_is_one_slice() {
    // A caller with no slice in scope builds one from the pointer and the
    // length; the slice is still one argument.
    prove(&format!(
        "import click::rust::slice;
        {SIZES}
        theorem size_is_length(p: *const u8, n: usize) {{
            ensures size(slice::from_raw_parts(p, n)) == n by {{
                unfold(size(slice::from_raw_parts(p, n)));
                close();
            }}
        }}
        theorem both_adds(p: *const u8, n: usize, k: usize) {{
            requires n <= 100u64;
            requires k <= 100u64;
            ensures to_integer(both(slice::from_raw_parts(p, n), k)) == to_integer(n + k) by {{
                unfold(both(slice::from_raw_parts(p, n), k));
                unfold(size(slice::from_raw_parts(p, n)));
                close();
            }}
        }}"
    ))
    .unwrap();
    // Passing the pointer and the length as two arguments is refused.
    let error = prove(&format!(
        "{SIZES}
        theorem spread(p: *const u8, n: usize) {{
            ensures size(p, n) == n by {{ unfold(size(p, n)); close(); }}
        }}"
    ))
    .unwrap_err();
    assert!(
        error.message().contains("each slice is one argument"),
        "{error:?}"
    );
    let file = parse(&format!("verifying \"slices.rs\"; {SIZES}")).unwrap();
    let both = file
        .click_function_definitions()
        .iter()
        .find(|function| function.name() == "both")
        .unwrap();
    let parameters = both
        .parameters()
        .iter()
        .map(|parameter| parameter.name())
        .collect::<Vec<_>>();
    // The slice is one parameter of the built-in slice type
    // (`design/rust-slice-values.md`), not its pointer and its length.
    assert_eq!(parameters, ["bytes", "bytes_len"]);
    assert_eq!(
        both.parameters()[0].click_type(),
        &ClickType::Program(InterfaceType::Slice(crate::kernel::SliceElement::UInt8)),
    );
}

#[test]
fn a_slice_argument_must_be_a_slice_parameter() {
    let error = prove(&format!(
        "{SIZES}
        theorem pointer(p: *const u8) {{
            ensures size(p) == 0u64 by {{ close(); }}
        }}"
    ))
    .unwrap_err();
    assert!(
        error.message().contains("`p` is not a slice parameter"),
        "{error:?}"
    );
}

/// A string slice is the wide pointer at its own type, `Str`
/// (`design/rust-slice-values.md`, "String slices"). Its methods are
/// `str`'s: `len()` and `as_ptr()` read its components, and `as_bytes()`
/// is the same data pointer and length as a byte slice, which
/// `str::from_utf8_unchecked` retypes back, all with no unfold.
#[test]
fn a_string_slice_reads_its_bytes_in_place() {
    prove(
        "import click::rust::slice;
        import click::rust::str;
        theorem bytes_of(s: &str) {
            ensures s.as_bytes().len() == s.len() by { close(); }
        }
        theorem data_of(s: &str) {
            ensures s.as_bytes().as_ptr() == s.as_ptr() by { close(); }
        }
        theorem round_trip(s: &str) {
            ensures str::from_utf8_unchecked(s.as_bytes()) == s by { close(); }
        }
        theorem built(p: *const u8, n: usize) {
            ensures str::from_utf8_unchecked(slice::from_raw_parts(p, n)).len() == n by { close(); }
        }",
    )
    .unwrap();
}

/// A string slice is no byte slice: a slice method it has not, a generic
/// `Slice<T>` parameter and a comparison with a byte slice each refuse it,
/// naming its type.
#[test]
fn a_string_slice_is_not_a_byte_slice() {
    for (claim, printed) in [
        ("s[0] == 0u8", "`Str` has no method `[]`"),
        ("s[0..1].len() == 1u64", "`Str` has no method"),
        ("slice::len(s) == 0u64", "Str"),
        ("s == s.as_bytes()", "Str"),
    ] {
        let error = prove(&format!(
            "import click::rust::slice;
            theorem claim(s: &str) {{
                ensures {claim} by {{ close(); }}
            }}"
        ))
        .err()
        .unwrap_or_else(|| panic!("`{claim}` must be refused"));
        assert!(
            error.message().contains(printed),
            "`{claim}` names `{printed}`: {error:?}"
        );
    }
}

/// A failed claim about a string slice states its goal with `str`'s own
/// operations.
#[test]
fn a_string_slice_failure_names_its_operations() {
    let error = prove(
        "import click::rust::slice;
        theorem claim(s: &str) {
            ensures s.as_bytes() == slice::from_raw_parts(s.as_ptr(), 1u64) by { close(); }
        }",
    )
    .unwrap_err();
    let message = format!("{error:?}");
    assert!(
        message.contains(
            "click::rust::str::as_bytes(s) == \
             click::rust::slice::from_raw_parts(click::rust::str::as_ptr(s), 1u64)"
        ),
        "{message}"
    );
}
