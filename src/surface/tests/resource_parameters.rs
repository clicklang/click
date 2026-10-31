use super::expansion_tests::mdtest_sources;
use super::*;

const ABSTRACT_PROOF: &str = r#"
import click::separation;
theorem restrict_again(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b) by {
        apply(separation::restrict(A, B, a, b)) using {
            separate(A, B);
            contains(A, a);
            contains(B, b);
        };
    }
}
"#;

#[test]
fn resource_parameters_apply_explicit_axiom_and_expand() {
    without_implicit_auto(|| verify_click_theorems(ABSTRACT_PROOF)).unwrap();
    let expanded =
        expand_c0_claim_source_by_label(ABSTRACT_PROOF, &[], "restrict_again.ensures_0").unwrap();
    assert!(expanded.contains("Resource"));
    without_implicit_auto(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
fn resource_parameters_require_every_listed_premise() {
    for premise in ["separate(A, B);", "contains(A, a);", "contains(B, b);"] {
        let missing = ABSTRACT_PROOF.replace(&format!("            {premise}"), "");
        assert!(
            without_implicit_auto(|| verify_click_theorems(&missing)).is_err(),
            "{premise}"
        );
    }
    let wrong = ABSTRACT_PROOF.replace("restrict(A, B, a, b)", "restrict(A, B, A, b)");
    assert!(without_implicit_auto(|| verify_click_theorems(&wrong)).is_err());
}

#[test]
fn resource_parameters_refuse_numeric_arguments() {
    let wrong = ABSTRACT_PROOF.replace("restrict(A, B, a, b)", "restrict(0, B, a, b)");
    assert!(verify_click_theorems(&wrong).is_err());
}

#[test]
fn resource_parameters_prove_field_separation_without_search() {
    let (source, sources) = mdtest_sources("mdtests/resource_theorem_parameters.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_auto(|| verify_c0_sources(&source, &sources)).unwrap();
}

#[test]
fn resource_parameters_capture_simultaneously() {
    let client = r#"
    theorem swapped(B: Resource, A: Resource, b: Resource, a: Resource) {
        requires separate(B, A);
        requires contains(B, b);
        requires contains(A, a);
        ensures separate(b, a) by {
            apply(restrict_again(B, A, b, a)) using {
                separate(B, A); contains(B, b); contains(A, a);
            };
        }
    }
    "#;
    without_implicit_auto(|| verify_click_theorems(&format!("{ABSTRACT_PROOF}{client}"))).unwrap();
}

#[test]
fn resource_parameters_accept_declared_descriptors() {
    let source = r#"
    abstract resource ticket(id: int32);
    resource cell(p: int32*) { owns *p; }
    theorem transport(A: Resource, B: Resource) {
        requires separate(A, B);
        ensures separate(A, B) by { assumption(); }
    }
    theorem declared(p: int32*, id: int32) {
        requires separate(cell(p), ticket(id));
        ensures separate(cell(p), ticket(id)) by {
            apply(transport(cell(p), ticket(id))) using {
                separate(cell(p), ticket(id));
            };
        }
    }
    "#;
    without_implicit_auto(|| verify_click_theorems(source)).unwrap();
    let expanded = expand_c0_claim_source_by_label(source, &[], "declared.ensures_0").unwrap();
    without_implicit_auto(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
fn resource_parameters_do_not_grant_ownership_or_numeric_values() {
    for source in [
        "theorem invalid(A: Resource) { owns A; ensures true; }",
        "theorem invalid(A: Resource) { produces A; ensures true; }",
        "theorem invalid(A: Resource) { ensures A == 0; }",
        "theorem numeric(x: int32) { ensures x == x; }\n\
         theorem invalid(A: Resource) { ensures 0 == 0 by { apply(numeric(A)); } }",
        "theorem invalid(A: Resource) { ensures separate(A, A) by { let A: int32 = 0; } }",
    ] {
        assert!(verify_click_theorems(source).is_err(), "{source}");
    }
}

#[test]
fn generic_pointer_parameters_subrange_and_expansion() {
    let (source, sources) = mdtest_sources("mdtests/generic_pointer_theorem_parameters.md");
    assert!(sources.is_empty());
    without_implicit_auto(|| verify_click_theorems(&source)).unwrap();
    for label in [
        "integers.ensures_0",
        "bytes.ensures_0",
        "pointers.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_auto(|| verify_click_theorems(&expanded)).unwrap();
    }
    for premise in ["lo <= a;", "a <= b;", "b <= hi;"] {
        let missing = source.replace(
            "using { lo <= a; a <= b; b <= hi; }",
            &format!(
                "using {{ {} }}",
                "lo <= a; a <= b; b <= hi;".replace(premise, "")
            ),
        );
        assert!(without_implicit_auto(|| verify_click_theorems(&missing)).is_err());
    }
}

#[test]
fn generic_pointer_parameters_require_consistent_element_types() {
    let source = r#"
        theorem same<T>(p: T*, q: T*) {
            ensures true by { normalize(); }
        }
        theorem wrong(p: int32*, q: uint8*) {
            ensures true by {
                apply(same(p, q)) using {};
            }
        }
    "#;
    let error = verify_click_theorems(source).unwrap_err();
    assert!(
        error.report().contains("type parameter"),
        "{}",
        error.report()
    );
}

#[test]
fn generic_pointer_struct_parameters_apply_and_expand() {
    let (source, sources) = mdtest_sources("mdtests/generic_pointer_struct_parameters.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_auto(|| verify_c0_sources(&source, &sources)).unwrap();
    for label in ["inspect.contract", "padded.ensures_0"] {
        let expanded = expand_c0_claim_source_by_label(&source, &sources, label).unwrap();
        without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
    }
    let verified =
        without_implicit_auto(|| verify_click_theorems_with_c_sources(&source, &sources)).unwrap();
    let padded = verified
        .iter()
        .find(|theorem| theorem.theorem_definition.name() == "padded")
        .unwrap();
    let Proposition::CResourceContains { parent, child } = &padded.conclusion else {
        panic!("expected containment");
    };
    for resource in [parent, child] {
        let crate::kernel::CResource::Memory(range) = resource.as_ref() else {
            panic!("expected memory");
        };
        assert_eq!(
            range.element_width(),
            16,
            "the padded struct keeps its physical stride"
        );
    }

    let no_origin = source.replace("theorem identity<T>", "theorem requires_item(p: struct item*) { ensures p == p by { normalize(); } }\ntheorem identity<T>")
        .replace("have p == p by { apply(identity(p)) using {}; }", "have p == p by { apply(identity(p)) using {}; }\n    have p == p by { apply(requires_item(p)) using {}; }");
    let error = without_implicit_auto(|| verify_c0_sources(&no_origin, &sources)).unwrap_err();
    assert!(
        error.report().contains("requires original object class"),
        "{}",
        error.report()
    );

    let wrong = source
        .replace(
            "theorem identity<T>(p: T*)",
            "theorem identity<T>(p: T*, q: T*)",
        )
        .replace("apply(identity(p))", "apply(identity(p, q))");
    let error = without_implicit_auto(|| verify_c0_sources(&wrong, &sources)).unwrap_err();
    assert!(
        error.report().contains("type parameter"),
        "{}",
        error.report()
    );
}

#[test]
fn elements_separation_applies_and_expands_without_implicit_search() {
    for (fixture, labels) in [
        ("mdtests/separation_elements.md", vec!["keep.contract"]),
        (
            "mdtests/separation_elements_types.md",
            vec!["words.ensures_0", "pointers.ensures_0", "inspect.contract"],
        ),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        without_implicit_auto(|| verify_c0_sources(&source, &sources)).unwrap();
        for label in labels {
            let expanded = expand_c0_claim_source_by_label(&source, &sources, label).unwrap();
            without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
        }
    }
}

#[test]
fn elements_separation_requires_distinct_indices() {
    for (requirement, arguments) in [("", "i, j"), ("requires i != j;", "i, i")] {
        let source = format!(
            r#"
            import click::separation;
            theorem invalid(p: uint8*, i: uint64, j: uint64) {{
                {requirement}
                ensures separate(memory(p[i]), memory(p[j])) by {{
                    apply(separation::elements(p, {arguments})) using {{}};
                }}
            }}
        "#
        );
        assert!(without_implicit_auto(|| verify_click_theorems(&source)).is_err());
    }
}
