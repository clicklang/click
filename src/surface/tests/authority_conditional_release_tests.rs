use super::*;

const C: &str = r#"struct child { int32 refs; int32 payload; };

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void release_one(struct child* obj) {
    child_release(obj);
}
"#;
const SOURCE: &str = r#"resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    contains allocation(obj, sizeof(struct child));
    owns object(obj);
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}


verifying "conditional_release.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
    ensures old(count(child_ref(obj))) > 1 implies obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        execute();
        simp();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            arithmetic() using { 1 <= obj->refs; obj->refs != 1; }
        }
        have obj->refs - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
                1 < obj->refs;
            }
        }
        step();
        step();
        fold(child_control(obj));
        execute();
        simp();
    }
}


void release_one(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    have obj->refs == count(child_ref(obj)) by { simp(); }
    have 1 < count(child_ref(obj)) by { simp(); }
    step(child_release(obj), {});
    have obj->payload == old(obj->payload) by { simp(); }
    step();
    simp();
}
"#;

fn verify(source: &str) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let project = ClickProject::new(
        "conditional_release.click",
        [ClickModuleSource::new(
            "conditional_release.click",
            source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
        resource_semantics: ResourceSemanticsMode::Authority,
    });
    verify_c0_project(&project, &[("conditional_release.c", C)])
}

#[test]
fn authority_conditional_release_certifies_its_resource_guard() {
    let source = SOURCE
        .split("void release_one(struct child* obj)")
        .next()
        .unwrap();
    verify(source).expect("the guarded resource claim certifies under both C branches");
}

#[test]
fn authority_conditional_release_certifies_both_lifetime_branches() {
    verify(SOURCE)
        .expect("nonfinal release restores control; final release retires authority and frees");
}

#[test]
fn authority_conditional_release_rejects_returning_control_after_free() {
    let source = SOURCE.replace("if old(obj->refs) > 1", "if old(obj->refs) >= 1");
    let error = verify(&source).expect_err("the final branch cannot return freed control");
    assert!(error.message().contains("child_control"), "{error:?}");
}

#[test]
fn authority_conditional_release_rejects_missing_returned_control_witness() {
    let source = SOURCE.replace("fold(child_control(obj));", "");
    verify(&source)
        .expect_err("a conditional claim key cannot replace its returned resource witness");
}

#[test]
fn authority_nonfinal_helper_postcondition_observes_updated_count() {
    let source = SOURCE.replace(
        "    ensures obj->payload == old(obj->payload);",
        "    ensures obj->payload == old(obj->payload);\n    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;",
    );
    verify(&source).expect("the caller observes the checked member delta in its postcondition");
}

#[test]
fn authority_conditional_release_keeps_undischarged_ensure_premise() {
    let source = SOURCE.replace(
        "old(count(child_ref(obj))) > 1 implies",
        "old(count(child_ref(obj))) > 2 implies",
    );
    verify(&source).expect_err("a checked count bound cannot assume the callee's stronger premise");
}

#[test]
fn authority_conditional_release_expansion_roundtrips_every_smart_site() {
    let source = SOURCE.replace(
        "    ensures obj->payload == old(obj->payload);",
        "    ensures obj->payload == old(obj->payload);\n    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;",
    );
    let project = ClickProject::new(
        "conditional_release.click",
        [ClickModuleSource::new(
            "conditional_release.click",
            &source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
        resource_semantics: ResourceSemanticsMode::Authority,
    });
    let c = [("conditional_release.c", C)];
    let sites = c0_project_smart_tactic_source_sites(&project, &c).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position =
            c0_project_tactic_source_position(&project, &c, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_project_tactic_source_at(&project, &c, position.line, position.column)
                .unwrap();
        verify(&expanded).unwrap_or_else(|error| {
            panic!(
                "{} site {} ({}) expansion failed: {}",
                site.claim_label,
                site.source_index,
                site.tactic_name,
                error.message()
            )
        });
    }
}
