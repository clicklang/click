use super::*;

fn prove(body: &str) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    verify_c0_sources(
        &format!("verifying \"slices.rs\"; {body}"),
        &[("slices.rs", "")],
    )
}

const SIZES: &str = "
    function size(bytes: &[u8]) -> usize { bytes.len() }
    function both(bytes: &[u8], extra: usize) -> usize { size(bytes) + extra }
";

#[test]
fn a_pure_function_slice_parameter_is_its_pointer_and_length() {
    // A caller with no slice in scope writes the pointer and the length.
    prove(&format!(
        "{SIZES}
        theorem size_is_length(p: *const u8, n: usize) {{
            ensures size(p, n) == n by {{ unfold(size(p, n)); normalize(); }}
        }}
        theorem both_adds(p: *const u8, n: usize, k: usize) {{
            requires n <= 100u64;
            requires k <= 100u64;
            ensures both(p, n, k) == n + k by {{
                unfold(both(p, n, k));
                unfold(size(p, n));
                normalize();
            }}
        }}"
    ))
    .unwrap();
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
    assert_eq!(parameters, ["bytes", "bytes_len", "extra"]);
}

#[test]
fn a_slice_argument_must_be_a_slice_parameter() {
    let error = prove(&format!(
        "{SIZES}
        theorem pointer(p: *const u8) {{
            ensures size(p) == 0u64 by {{ normalize(); }}
        }}"
    ))
    .unwrap_err();
    assert!(
        error.message().contains("`p` is not a slice parameter"),
        "{error:?}"
    );
}
