use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/trait-methods/shapes.click");

fn trait_methods_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/trait-methods");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A crate trait method's contract is its interface. A call through a trait
// bound or a `&dyn` reference assumes it of whichever implementation it
// reaches, so each implementation inherits its guarantees, which its proof
// establishes, and must accept every call it allows. The interface reads nothing
// through `self`, whose type it does not know.
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn charon_trait_method_implementations_refine_their_interface() {
    let p = trait_methods_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (edits, expected) in [
        // An implementation inherits the interface's guarantee, which its
        // proof must establish.
        (
            &[(
                "        ensures scale < result and result <= 3001;\n    }\n    fn twice",
                "        ensures scale < result and result <= 2000;\n    }\n    fn twice",
            )][..],
            "`<trait_methods::Square as trait_methods::Shape>::area.interface_ensures_0`",
        ),
        // Its clauses read the same only under the interface's names.
        (
            &[(
                "    fn area(&self, scale: i32) -> i32 {\n        ensures result == scale + scale + 1;",
                "    fn area(&self, s: i32) -> i32 {\n        ensures result == s + s + 1;",
            )][..],
            "`<trait_methods::Circle as trait_methods::Shape>::area` cannot inherit its trait's interface: an implementation names its parameters as the trait's interface does",
        ),
        // An implementation that refuses a call the interface allows.
        (
            &[(
                "        requires scale <= 2000;\n",
                "        requires scale <= 500;\n",
            )][..],
            "`<trait_methods::Square as trait_methods::Shape>::area` does not refine",
        ),
        // A call through the trait knows only the interface, not which
        // implementation it reaches.
        (
            &[(
                "fn trait_methods::through_dyn(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures scale < result;",
                "fn trait_methods::through_dyn(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures result == scale + scale + 1;",
            )][..],
            "trait_methods::through_dyn.ensures_0",
        ),
        // Without an interface for `area`, a call through the trait has no
        // contract.
        (
            &[
                (
                    "    fn area(&self, scale: i32) -> i32 {\n        requires 0 <= scale and scale <= 1000;\n        ensures scale < result and result <= 3001;\n    }\n",
                    "",
                ),
                // Circle then inherits no bounds; it states its own.
                (
                    "        ensures result == scale + scale + 1;\n",
                    "        requires 0 <= scale and scale <= 1000;\n        ensures result == scale + scale + 1;\n",
                ),
            ][..],
            "cannot execute call to `trait_methods::Shape::area`",
        ),
        // The interface has no field of `self` to read, nor its resources.
        (
            &[(
                "        ensures scale < result and result <= 3001;\n    }\n    fn twice",
                "        ensures scale < result and result <= 3001;\n        ensures self.side == 3;\n    }\n    fn twice",
            )][..],
            "a trait method's interface reads nothing through `self`",
        ),
        (
            &[(
                "        ensures scale < result and result <= 3001;\n    }\n    fn twice",
                "        views self.side;\n        ensures scale < result and result <= 3001;\n    }\n    fn twice",
            )][..],
            "a trait method's interface holds no resources",
        ),
        // An implementation must be verified against its own contract.
        (
            &[(
                "impl trait_methods::Shape for trait_methods::Circle {\n    fn area(&self, scale: i32) -> i32 {\n        ensures result == scale + scale + 1;\n    } by { execute(); simp(); }\n    fn twice(&self, scale: i32) -> i32 {\n        ensures result == scale + 3;\n    } by { execute(); simp(); }\n}\n",
                "",
            )][..],
            "`<trait_methods::Circle as trait_methods::Shape>::area` implements the trait method interface `trait_methods::Shape::area` but has no contract",
        ),
        // A trait-bound parameter is a reference to a value of unknown type,
        // not to one implementation's.
        (
            &[(
                "(shape: &T, scale: i32)",
                "(shape: &trait_methods::Square, scale: i32)",
            )][..],
            "signature mismatch for `trait_methods::total` parameter 1",
        ),
        // A default method's body is verified against its own contract,
        // its calls of `area` assuming `area`'s interface.
        (
            &[(
                "        ensures result <= 6002;\n    } by { execute(); simp(); }\n}",
                "        ensures result <= 5000;\n    } by { execute(); simp(); }\n}",
            )][..],
            "trait_methods::Shape::twice.ensures_0",
        ),
        // An override of a default method inherits its contract and must
        // accept every call it allows.
        (
            &[(
                "    fn twice(&self, scale: i32) -> i32 {\n        ensures result == scale + 3;",
                "    fn twice(&self, scale: i32) -> i32 {\n        requires 0 <= scale and scale <= 10;\n        ensures result == scale + 3;",
            )][..],
            "does not refine the trait method interface `trait_methods::Shape::twice`",
        ),
        // A call on a type that keeps the default gets the default's
        // contract, and no more.
        (
            &[(
                "fn trait_methods::direct_default(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures result <= 6002;",
                "fn trait_methods::direct_default(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures result <= 6001;",
            )][..],
            "trait_methods::direct_default.ensures_0",
        ),
    ] {
        let mut invalid = SIDECAR.to_string();
        for (before, after) in edits {
            assert!(invalid.contains(before), "{before}");
            invalid = invalid.replacen(before, after, 1);
        }
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("an implementation or call the interface does not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 15s in the parallel gate"]
fn charon_trait_methods_tools_recheck_expanded_certificates() {
    let p = trait_methods_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I13_trait_methods_I5_total.contract",
        "__rust_q_I13_trait_methods_I7_dynamic.contract",
        "<trait_methods::Circle as trait_methods::Shape>::area.contract",
        "trait_methods::Shape::twice.contract",
        "<trait_methods::Circle as trait_methods::Shape>::twice.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
