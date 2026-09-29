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
fn authority_helper_returns_member_with_private_memory_body() {
    let c_source = r#"
        int32 helper(int32* p) { *p = 7; return 7; }
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            int32 result = helper(p);
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 helper(int32* p) {
            owns authority(reference(p));
            owns reference(p);
            ensures result == 7;
        } by {
            open(reference(p)) { step(); }
            execute();
            simp();
        }

        int32 value() {
            ensures result == 0 or result == 7;
        } by {
            step();
            step();
            branch {
                then { execute(); simp(); }
                else {}
            }
            fold(authority(reference(p)));
            fold(reference(p));
            step();
            step();
            unfold(reference(p));
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("a checked helper returns the same private-body member");
}

#[test]
fn authority_helpers_create_and_consume_member_with_private_memory_body() {
    let c_source = r#"
        int32 acquire(int32* p) { p[0] = 7; p[1] = 9; return 7; }
        int32 release(int32* p) { p[0] = 7; p[1] = 9; return 7; }
        int32 value(void) {
            int32* p = malloc(8);
            if (p == 0) return 0;
            int32 result = acquire(p);
            release(p);
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) {
            owns p[0..1];
            owns p[1..2];
        }
        verifying "private_body.c";

        int32 acquire(int32* p) {
            owns authority(reference(p));
            consumes p[0..1];
            consumes p[1..2];
            produces reference(p);
            ensures result == 7;
        } by {
            step();
            step();
            fold(reference(p));
            execute();
            simp();
        }

        int32 release(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            produces p[0..1];
            produces p[1..2];
            ensures result == 7;
        } by {
            unfold(reference(p));
            step();
            step();
            execute();
            simp();
        }

        int32 value() {
            ensures result == 0 or result == 7;
        } by {
            step();
            step();
            branch {
                then { execute(); simp(); }
                else {}
            }
            fold(authority(reference(p)));
            step();
            step();
            have count(reference(p)) == 1 by { simp(); }
            step();
            have count(reference(p)) == 0 by { simp(); }
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("verified helpers move the private body with one member birth and death");
}

#[test]
fn authority_creating_helper_requires_caller_private_body() {
    let c_source = r#"
        int32 acquire(int32* p) { *p = 7; return 7; }
        int32 value(void) {
            int32 x = 7;
            return acquire(&x);
        }
    "#;
    let click_source = r#"
        resource reference(p: int32*) { owns p[0..1]; }
        verifying "private_body.c";
        int32 acquire(int32* p) {
            owns authority(reference(p));
            consumes p[0..1];
            produces reference(p);
            ensures result == 7;
        } by {
            step();
            fold(reference(p));
            execute();
            simp();
        }
        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("authority and local storage do not supply a separable private body");
    assert!(
        error
            .message()
            .contains("missing resource fact `owns x[0..1]`"),
        "{error:?}"
    );
}

#[test]
fn authority_consuming_helper_cannot_return_the_wrong_private_body() {
    let c_source = r#"int32 release(int32* p) { return 7; }"#;
    let click_source = r#"
        resource reference(p: int32*) { owns p[0..1]; }
        verifying "private_body.c";
        int32 release(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            produces p[1..2];
            ensures result == 7;
        } by {
            unfold(reference(p));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("the returned private body must match the member definition");
    assert!(
        error
            .message()
            .contains("missing resource fact `owns p[1..2]`"),
        "{error:?}"
    );
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
