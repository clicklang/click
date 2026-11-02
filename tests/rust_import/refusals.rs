use super::*;

/// An import refusal says where it is and what it refused: the source line
/// and function or struct field, the type as Rust writes it, and the callee
/// of a library call the importer has no model of.
#[test]
fn rust_import_refusals_name_their_place_and_construct() {
    for (source, expected) in [
        (
            "pub fn bad(n: u32) -> u32 {\n    let mut t = 0;\n    for i in (0..n).rev() { t = i; }\n    t\n}",
            &["borrow.rs:3 in bad:", "type `Rev<Range<u32>>`"][..],
        ),
        (
            "pub fn bad(a: u32, b: u32) -> u32 {\n    a.pow(b)\n}",
            &[
                "borrow.rs:2 in bad:",
                "unmodeled external call to `u32::pow`",
            ],
        ),
        (
            "pub struct Inner { pub a: u32 }\npub struct Outer { pub inner: Inner }\npub fn bad(o: &Outer) -> u32 { o.inner.a }",
            &[
                "borrow.rs:2 in struct `Outer`, field `inner`:",
                "nested owned field",
            ],
        ),
    ] {
        let error = Project::new(source).refresh().unwrap_err();
        for expected in expected {
            assert!(error.contains(expected), "{expected}: {error}");
        }
    }
}
