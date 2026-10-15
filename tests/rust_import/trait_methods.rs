use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/trait-methods/shapes.click");

fn trait_methods_project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "shapes.rs",
            include_bytes!("../../design/charon-trial/trait-methods/shapes.rs").as_slice(),
        ),
        ("borrow.click", SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/trait-methods/shapes.click.import.json")
                .as_slice(),
        ),
        (
            "shapes.ullbc",
            include_bytes!("../../design/charon-trial/trait-methods/shapes.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/trait-methods/shapes.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

// A crate trait method's contract is its interface. A call through a trait
// bound or a `&dyn` reference assumes it of whichever implementation it
// reaches, so each implementation must refine it: accept every call it
// allows and guarantee what it promises. The interface reads nothing
// through `self`, whose type it does not know.
#[test]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn charon_trait_method_implementations_refine_their_interface() {
    let p = trait_methods_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // An implementation that does not state the interface's guarantee.
        (
            "        ensures result == scale + scale + 1;\n        ensures scale < result and result <= 3001;\n",
            "        ensures result == scale + scale + 1;\n",
            "`<trait_methods::Circle as trait_methods::Shape>::area` does not refine the trait method interface `trait_methods::Shape::area`",
        ),
        // An implementation that refuses a call the interface allows.
        (
            "        requires scale <= 2000;\n",
            "        requires scale <= 500;\n",
            "`<trait_methods::Square as trait_methods::Shape>::area` does not refine",
        ),
        // A call through the trait knows only the interface, not which
        // implementation it reaches.
        (
            "fn trait_methods::through_dyn(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures scale < result;",
            "fn trait_methods::through_dyn(scale: i32) -> i32 {\n    requires 0 <= scale and scale <= 1000;\n    ensures result == scale + scale + 1;",
            "trait_methods::through_dyn.ensures_0",
        ),
        // Without the `trait` block, a call through the trait has no contract.
        (
            "trait trait_methods::Shape {\n    fn area(&self, scale: i32) -> i32 {\n        requires 0 <= scale and scale <= 1000;\n        ensures scale < result and result <= 3001;\n    }\n}\n",
            "",
            "cannot execute call to `trait_methods::Shape::area`",
        ),
        // The interface has no field of `self` to read, nor its resources.
        (
            "        ensures scale < result and result <= 3001;\n    }\n}",
            "        ensures scale < result and result <= 3001;\n        ensures self.side == 3;\n    }\n}",
            "a trait method's interface reads nothing through `self`",
        ),
        (
            "        ensures scale < result and result <= 3001;\n    }\n}",
            "        views self.side;\n        ensures scale < result and result <= 3001;\n    }\n}",
            "a trait method's interface holds no resources",
        ),
        // A trait-bound parameter is a reference to a value of unknown type,
        // not to one implementation's.
        (
            "(shape: &T, scale: i32)",
            "(shape: &trait_methods::Square, scale: i32)",
            "signature mismatch for `trait_methods::total` parameter 1",
        ),
    ] {
        let invalid = SIDECAR.replacen(before, after, 1);
        assert_ne!(invalid, SIDECAR, "{before}");
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("an implementation or call the interface does not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 5.2s in the parallel gate"]
fn charon_trait_methods_tools_recheck_expanded_certificates() {
    let p = trait_methods_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I13_trait_methods_I5_total.contract",
        "__rust_q_I13_trait_methods_I7_dynamic.contract",
        "<trait_methods::Circle as trait_methods::Shape>::area.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
