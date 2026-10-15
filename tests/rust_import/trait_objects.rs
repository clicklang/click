use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/trait-objects/shapes.click");

fn trait_objects_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/trait-objects");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A trait's `function`s are its object's state. An interface reads them of
// the object a `&self`, bound-parameter, or `&dyn` reference holds; each
// implementation defines them from its own fields and is verified on its
// memory against the interface read through those definitions; and a caller
// that passes a struct as the object knows the struct's definitions.
#[test]
#[ignore = "nightly: 3.3s in the parallel gate"]
fn charon_trait_object_functions_are_defined_per_implementation() {
    let p = trait_objects_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // An implementation's definition must make its body meet the
        // interface's guarantee.
        (
            "function size(self) -> i32 { self.radius + self.radius }",
            "function size(self) -> i32 { self.radius }",
            "`<trait_objects::Circle as trait_objects::Shape>::area.interface_ensures_0`",
        ),
        // An implementation that refuses a call the interface allows.
        (
            "    fn area(&self, scale: i32) -> i32 {\n    } by { execute(); simp(); }\n}\n\nimpl trait_objects::Shape for trait_objects::Circle",
            "    fn area(&self, scale: i32) -> i32 {\n        requires 0 <= scale and scale <= 50;\n        requires 0 <= self.side and self.side <= 100;\n    } by { execute(); simp(); }\n}\n\nimpl trait_objects::Shape for trait_objects::Circle",
            "`<trait_objects::Square as trait_objects::Shape>::area` does not refine",
        ),
        // A caller knows the definition of the struct it passes.
        (
            "    ensures result == 4 + scale;",
            "    ensures result == 3 + scale;",
            "trait_objects::through_dyn.ensures_0",
        ),
        // Every implementation defines each of the trait's functions.
        (
            "    function size(self) -> i32 { self.side }\n",
            "",
            "defines it for its type",
        ),
    ] {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a definition or call the interface does not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 8.2s in the parallel gate"]
fn charon_trait_objects_tools_recheck_expanded_certificates() {
    let p = trait_objects_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I13_trait_objects_I5_total.contract",
        "__rust_q_I13_trait_objects_I11_through_dyn.contract",
        "<trait_objects::Circle as trait_objects::Shape>::area.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
