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
fn a_pure_function_slice_parameter_is_its_pointer_and_length() {
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
    assert_eq!(parameters, ["bytes", "bytes.len()", "bytes_len"]);
    assert_eq!(
        both.parameters()[1].binding_name(),
        crate::kernel::BindingName::slice_length("bytes"),
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
