use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/core-methods/methods.click");

/// A call of a Rust core integer method calls an external function whose
/// contract the library supplies, stating its result with the library's
/// function of the same path: claims written with `u32::min(a, b)` verify,
/// a wrong claim about one is refused, and each definition is Rust's at the
/// edge of its type.
#[test]
fn charon_core_methods_verify_against_their_library_contracts() {
    let p = Project::from_fixture("design/charon-trial/core-methods");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let imports = SIDECAR
        .lines()
        .take_while(|line| line.starts_with("import "))
        .collect::<Vec<_>>()
        .join("\n");
    for (before, after, expected) in [
        // `min` is not `max`.
        (
            "    ensures result == u32::min(a, b);\n",
            "    ensures result == u32::max(a, b);\n",
            "smaller",
        ),
        // A sum that fits is `Some`, never `None`.
        (
            "    have u32::checked_add(a, b) == Option<u32>::Some(a + b) by {\n",
            "    have u32::checked_add(a, b) == Option<u32>::None by {\n",
            "clamp_add",
        ),
        // `i8::wrapping_add` wraps to the minimum, not to the maximum.
        (
            "    ensures i8::wrapping_add(127i8, 1i8) == -128i8 by {\n",
            "    ensures i8::wrapping_add(127i8, 1i8) == 127i8 by {\n",
            "i8_wrapping_add_wraps",
        ),
    ] {
        // Only the item that holds the change is verified again.
        let item = SIDECAR
            .split("\nfn ")
            .flat_map(|chunk| chunk.split("\ntheorem "))
            .skip(1)
            .find(|item| item.contains(before))
            .unwrap_or_else(|| panic!("{before}"));
        let keyword = if SIDECAR.contains(&format!("\ntheorem {}", item.lines().next().unwrap())) {
            "theorem"
        } else {
            "fn"
        };
        let invalid = format!(
            "{imports}\nverifying \"methods.rs\";\n{keyword} {}",
            item.replacen(before, after, 1)
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
    // A sidecar names the library function only after importing its module.
    let unimported = SIDECAR.replacen("import click::rust::u32;\n", "", 1);
    assert!(C0VerificationSession::new_program_prepared(&unimported, &prepared).is_err());
}
