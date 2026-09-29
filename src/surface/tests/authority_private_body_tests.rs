use super::*;

fn project(click_source: &str) -> ClickProject {
    ClickProject::new(
        "private_body.click",
        [ClickModuleSource::new(
            "private_body.click",
            click_source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
        resource_semantics: ResourceSemanticsMode::Authority,
    })
}

#[test]
fn authority_member_local_body_requires_explicit_ownership() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            have count(reference(&x)) == 1 by { simp(); }
            unfold(reference(&x));
            have count(reference(&x)) == 0 by { simp(); }
            unfold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("local storage alone does not provide a separable body resource");
    assert!(
        error.message().contains("Requires the private body"),
        "{error:?}"
    );
}

#[test]
fn authority_member_private_heap_body_round_trip() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            free(p);
            return 1;
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch {
                then {
                    execute();
                    simp();
                }
                else {}
            }
            fold(authority(reference(p)));
            fold(reference(p));
            open(reference(p)) {
                have count(reference(p)) == 1 by { simp(); }
            }
            unfold(reference(p));
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("fresh heap ownership can back a member and its private body");
}

#[test]
fn authority_member_private_heap_body_cannot_back_two_births() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            free(p);
            return 1;
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch {
                then { execute(); simp(); }
                else {}
            }
            fold(authority(reference(p)));
            fold(reference(p));
            fold(reference(p));
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("one exclusive private memory body cannot create two members");
    assert!(
        error.message().contains("Requires the private body"),
        "{error:?}"
    );
}

#[test]
fn authority_mode_malloc_statement_evidence_starts_at_running_state() {
    let c_source =
        "int32 value(void) { int32* p; p = malloc(4); if (p == 0) return 0; free(p); return 0; }";
    let click_source = r#"
        verifying "private_body.c";
        int32 value() {
            ensures result == 0;
        } by {
            step();
            step();
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("malloc statement evidence must start at the current proof state");
}
