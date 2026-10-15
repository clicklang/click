use super::*;

const READER: &str = "int32 read_word(uint64 word, int32* p) { return *(int32*)word; }";

fn reader_contract(origin: &str) -> String {
    format!(
        r#"verifying "word.c";
        int32 read_word(uint64 word, int32* p) {{
            {origin}
            requires word == (uint64)p;
            views *p;
            ensures result == *p;
        }} by {{ execute(); simp(); }}"#
    )
}

#[test]
fn opaque_integer_pointer_inputs_require_explicit_origin() {
    let source = reader_contract("requires pointer_origin(word, p);");
    verify_c0_sources(&source, &[("word.c", READER)]).unwrap();
    let error = verify_c0_sources(&reader_contract(""), &[("word.c", READER)]).unwrap_err();
    assert!(error.to_string().contains("pointer_origin"), "{error}");
}

#[test]
fn pointer_integer_roundtrip_keeps_scalar_endpoint() {
    let c = "struct Pair { int32 first; int32 second; }; int32 probe(struct Pair* p) { return *((int32*)(uint64)(&p->first + 1)); }";
    let proof = r#"verifying "word.c";
        int32 probe(struct Pair* p) { views p->first; views p->second; ensures result == p->second; }
        by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("word.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
}

#[test]
fn checked_integer_origin_promise_preserves_selected_scalar() {
    let c = format!(
        "struct Pair {{ int32 first; int32 second; }}; {READER} int32 probe(struct Pair* p) {{ return read_word((uint64)&p->first, &p->first); }}"
    );
    let proof = format!(
        r#"{}
        int32 probe(struct Pair* p) {{ views p->first; ensures result == p->first; }} by {{ execute(); simp(); }}"#,
        reader_contract("requires pointer_origin(word, p);")
    );
    verify_c0_sources(&proof, &[("word.c", c.as_str())]).unwrap();
    let bad_c = c.replace(
        "(uint64)&p->first, &p->first",
        "(uint64)(&p->first + 1), &p->second",
    );
    let bad_proof = proof.replace(
        "views p->first; ensures result == p->first;",
        "views p->first; views p->second; ensures result == p->second;",
    );
    assert!(verify_c0_sources(&bad_proof, &[("word.c", bad_c.as_str())]).is_err());
}

#[test]
fn numeric_pointer_alias_does_not_issue_input_domain() {
    let c = "int32 read(int32* p, int32* q) { return *p; }";
    let proof = r#"verifying "alias.c"; int32 read(int32* p, int32* q) {
        requires p == q; views *q; ensures result == *q;
    } by { execute(); simp(); }"#;
    assert!(verify_c0_sources(proof, &[("alias.c", c)]).is_err());
}

#[test]
fn selecting_an_opaque_alias_field_does_not_authenticate_its_origin() {
    let c = "struct Pair { int32 first; int32 second; }; int32 read(struct Pair* p, struct Pair* q) { return q->first; }";
    let proof = r#"verifying "alias.c";
        int32 read(struct Pair* p, struct Pair* q) {
            requires p == q;
            views p->first;
            ensures result == p->first;
        } by { execute(); simp(); }"#;
    assert!(verify_c0_sources(proof, &[("alias.c", c)]).is_err());
    let promised = proof.replace(
        "requires p == q;",
        "requires p == q; requires pointer_origin(q, p);",
    );
    verify_c0_sources(&promised, &[("alias.c", c)]).unwrap();
}

#[test]
fn opaque_pointer_aliases_require_a_complete_origin_promise() {
    let c = "int32 read(int32* p, int32* q) { return *p; }";
    let proof = r#"verifying "alias.c"; int32 read(int32* p, int32* q) {
        requires pointer_origin(p, q);
        requires p == q;
        views *q;
        ensures result == *q;
    } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("alias.c", c)]).unwrap();
}

#[test]
fn numeric_equalities_cannot_forge_origin_promises() {
    verify_c0_sources(
        "theorem reflexive(p: int32*) { ensures pointer_origin(address(p), p) by { simp(); } }",
        &[],
    )
    .unwrap();
    for proof in [
        r#"theorem forge(p: int32*, q: int32*) {
            requires p == q;
            ensures pointer_origin(address(p), q) by { rewrite(p == q); simp(); }
        }"#,
        r#"predicate carries(word: uint64, p: int32*) { pointer_origin(word, p) }
        theorem forge(p: int32*, q: int32*) {
            requires p == q;
            requires carries(address(p), p);
            ensures carries(address(p), q) by { assumption(); }
        }"#,
    ] {
        assert!(verify_c0_sources(proof, &[]).is_err(), "{proof}");
    }
}

#[test]
fn scalar_domain_returns_survive_integer_helpers() {
    let proof = r#"verifying "saved.c";
        uint64 saved(struct Pair* p) { views p->first; ensures result == address(&p->first); }
        by { execute(); simp(); }
        int32 probe(struct Pair* p) { views p->first; views p->second; ensures result == p->first; }
        by { execute(); simp(); }"#;
    let c = "struct Pair { int32 first; int32 second; }; uint64 saved(struct Pair* p) { return (uint64)&p->first; } int32 probe(struct Pair* p) { return *((int32*)saved(p)); }";
    verify_c0_sources(proof, &[("saved.c", c)]).unwrap();
    let invalid = c.replace("*((int32*)saved(p))", "*(((int32*)saved(p)) + 1)");
    assert!(
        verify_c0_sources(
            &proof.replace("result == p->first", "result == p->second"),
            &[("saved.c", invalid.as_str())]
        )
        .is_err()
    );
}

#[test]
fn inferred_call_displacements_check_the_actual_input_even_without_a_dereference() {
    let c = "struct Pair { int32 first; int32 second; }; int32* advance(int32* p) { return p + 1; } int32* probe(struct Pair* p) { return advance(&p->first + 1); }";
    let proof = r#"verifying "advance.c";
        int32* advance(int32* p) {
            requires viewable(p[0..1]); ensures result == p + 1;
        } by { execute(); simp(); }
        int32* probe(struct Pair* p) {
            views p->first; views p->second; ensures true;
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("advance.c", c)]).unwrap_err();
    assert_eq!(error.kind(), ClickErrorKind::Proof);
    verify_c0_sources(
        proof,
        &[(
            "advance.c",
            c.replace("advance(&p->first + 1)", "advance(&p->first)")
                .as_str(),
        )],
    )
    .unwrap();
}

#[test]
fn viewability_cannot_widen_a_scalar_domain_at_a_void_helper() {
    let c = "struct Pair { int32 first; int32 second; }; void advance(int32* p) { p = p + 1; } int32 probe(struct Pair* p) { advance(&p->first + 1); return 0; }";
    let proof = r#"verifying "advance.c";
        void advance(int32* p) { requires viewable(p[0..1]); ensures true; }
        by { execute(); simp(); }
        int32 probe(struct Pair* p) {
            views p->first; views p->second; ensures result == 0;
        } by { execute(); simp(); }"#;
    assert!(verify_c0_sources(proof, &[("advance.c", c)]).is_err());
    verify_c0_sources(
        proof,
        &[(
            "advance.c",
            c.replace("advance(&p->first + 1)", "advance(&p->first)")
                .as_str(),
        )],
    )
    .unwrap();
}

#[test]
fn input_origin_promises_do_not_ignore_pointer_displacement() {
    let prefix = r#"theorem shifted(p: int32*) {
        requires viewable(p[0..2]);
        requires pointer_origin(p, p);
    "#;
    verify_c0_sources(
        &format!("{prefix} ensures pointer_origin(p + 1, p + 1) by {{ simp(); }} }}"),
        &[],
    )
    .unwrap();
    let error = verify_c0_sources(
        &format!("{prefix} ensures pointer_origin(p + 1, p) by {{ assumption(); }} }}"),
        &[],
    )
    .unwrap_err();
    assert_eq!(error.kind(), ClickErrorKind::Proof);
}

#[test]
fn checked_helper_stores_preserve_the_complete_pointer_cell() {
    let c = "struct Pair { int32 first; int32 second; }; struct Holder { int32* link; }; int32 save(struct Pair* p, struct Holder* h) { h->link = &p->first; return 0; } int32 keep(struct Holder* h) { return 0; } int32 probe(struct Pair* p, struct Holder* h) { save(p, h); keep(h); return *(h->link + 0); }";
    let proof = r#"verifying "stored.c";
    int32 save(struct Pair* p, struct Holder* h) {
        owns h->link; views p->first;
        requires separate(memory(h->link), memory(p->first));
        ensures h->link == &p->first;
        ensures result == 0;
    } by { execute(); simp(); }
    int32 keep(struct Holder* h) {
        owns h->link; ensures h->link == old(h->link); ensures result == 0;
    } by { execute(); simp(); }
    int32 probe(struct Pair* p, struct Holder* h) {
        owns h->link; views p->first; views p->second;
        requires separate(memory(h->link), memory(p->first));
        requires separate(memory(h->link), memory(p->second));
        ensures result == p->first;
    } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("stored.c", c)]).unwrap();
    let invalid = c.replace("h->link + 0", "h->link + 1");
    let error = verify_c0_sources(
        &proof.replace("ensures result == p->first", "ensures result == p->second"),
        &[("stored.c", invalid.as_str())],
    )
    .unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
}

#[test]
fn loaded_pointer_returns_preserve_domains_at_the_call_site() {
    let c = "struct Pair { int32 first; int32 second; }; struct Holder { int32* link; }; int32* get(struct Holder* h) { return h->link; } int32 probe(struct Pair* p, struct Holder* h) { h->link = &p->first; return *(get(h) + 0); }";
    let proof = r#"verifying "getter.c";
    int32* get(struct Holder* h) { views h->link; ensures result == h->link; }
    by { execute(); simp(); }
    int32 probe(struct Pair* p, struct Holder* h) {
        owns h->link; views p->first; views p->second;
        requires separate(memory(h->link), memory(p->first));
        requires separate(memory(h->link), memory(p->second));
        ensures result == p->first;
    } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("getter.c", c)]).unwrap();
    let invalid = c.replace("get(h) + 0", "get(h) + 1");
    let error = verify_c0_sources(
        &proof.replace("result == p->first", "result == p->second"),
        &[("getter.c", invalid.as_str())],
    )
    .unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
}

#[test]
fn nullable_result_domain_does_not_authorize_arithmetic_on_null() {
    let c = "struct Pair { int32 first; int32 second; }; int32* maybe(struct Pair* p, int32 flag) { if (flag) { return &p->first; } return 0; } int32 probe(struct Pair* p) { int32* q = maybe(p, 0); return q + 1 != 0; }";
    let proof = r#"verifying "nullable.c";
    int32* maybe(struct Pair* p, int32 flag) {
        views p->first;
        ensures flag == 0 implies result == 0;
        ensures flag != 0 implies result == &p->first;
    } by { execute(); simp(); }
    int32 probe(struct Pair* p) { views p->first; ensures result == result; }
    by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("nullable.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    verify_c0_sources(
        proof,
        &[("nullable.c", c.replace("q + 1", "q + 0").as_str())],
    )
    .unwrap();
}

#[test]
fn selected_array_members_allow_chained_valid_traversal() {
    let c = "struct Cells { int32 values[4]; int32 sibling; }; int32 probe(struct Cells* p, int32 i) { int32* q = &p->values[0]; q = q + i; q = q + 1; return *q; }";
    let proof = r#"verifying "array.c";
        int32 probe(struct Cells* p, int32 i) {
            views p->values[0..4];
            requires 0 <= i; requires i < 3;
            ensures result == result;
        } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("array.c", c)]).unwrap();
}

#[test]
fn numeric_aliases_cannot_issue_domains_at_a_modular_reader_call() {
    let c =
        "int32 read(int32* p) { return *p; } int32 probe(int32* p, int32* q) { return read(p); }";
    let proof = r#"verifying "call.c";
        int32 read(int32* p) { views *p; ensures result == *p; } by { execute(); simp(); }
        int32 probe(int32* p, int32* q) { requires p == q; views *q; ensures result == *q; }
        by { execute(); simp(); }"#;
    assert!(verify_c0_sources(proof, &[("call.c", c)]).is_err());
    verify_c0_sources(
        &proof.replace(
            "requires p == q;",
            "requires pointer_origin(p, q); requires p == q;",
        ),
        &[("call.c", c)],
    )
    .unwrap();
}

#[test]
fn mixed_return_paths_cannot_promote_a_scalar_endpoint_to_its_sibling() {
    let c = "struct Pair { int32 first; int32 second; }; int32* choose(struct Pair* p, int32 which) { if (which) return &p->first + 1; return &p->second; } int32 probe(struct Pair* p, int32 which) { return *choose(p, which); }";
    let proof = r#"verifying "choice.c";
        int32* choose(struct Pair* p, int32 which) {
            views p->first; views p->second; ensures result == &p->second;
        } by { execute(); simp(); }
        int32 probe(struct Pair* p, int32 which) {
            views p->first; views p->second; ensures result == result;
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("choice.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    verify_c0_sources(
        proof,
        &[(
            "choice.c",
            c.replace("&p->first + 1", "&p->second").as_str(),
        )],
    )
    .unwrap();
}

#[test]
fn pure_array_models_use_explicit_input_origin_promises() {
    let c = "void probe(int32* p, int32* q) {}";
    let proof = r#"verifying "model.c";
        function first(p: int32[]) -> int32 { p[0] }
        void probe(int32* p, int32* q) {
            requires pointer_origin(p, q);
            requires p == q;
            views *q;
            requires first(p) == 7;
            ensures first(q) == 7;
        } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("model.c", c)]).unwrap();
}

#[test]
fn scalar_domains_survive_expansion_and_retained_proof_edits() {
    let c = [(
        "scalar.c",
        "struct Pair { int32 first; int32 second; }; int32 probe(struct Pair* p) { return *(&p->first + 0); }",
    )];
    let proof = r#"verifying "scalar.c";
        int32 probe(struct Pair* p) {
            views p->first; views p->second; ensures result == p->first;
        } by { execute(); simp(); }"#;
    let expanded = expand_c0_claim_source(proof, &c, "probe", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &c).unwrap();
    let (session, _) = C0VerificationSession::new(proof, &c).unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("ensures result").unwrap());
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    let forged = proof.replace(
        "execute();",
        "have pointer_origin(&p->first + 1, &p->second) by simp; execute();",
    );
    let position = expansion::position_at_offset(&forged, forged.find("ensures result").unwrap());
    assert!(
        session
            .verify_at(&forged, position.line, position.column)
            .is_err()
    );
}

#[test]
fn opaque_callback_returns_require_an_origin_to_move_within_a_domain() {
    let c = "struct Pair { int32 first; int32 second; }; int32* probe(struct Pair* p, int32* (*f)(int32*)) { return f(&p->first) + 1; }";
    let proof = r#"verifying "callback.c";
        contract int32* End(int32* p) { views *p; ensures result == p + 1; }
        int32* probe(struct Pair* p, int32* (*f)(int32*)) {
            requires End(f); views p->first; views p->second;
            ensures result == &p->second + 1;
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("callback.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    let reflexive = proof.replace(
        "ensures result == p + 1;",
        "ensures result == p + 1; ensures pointer_origin(result, result);",
    );
    assert!(verify_c0_sources(&reflexive, &[("callback.c", c)]).is_err());
    let promised = proof.replace(
        "ensures result == p + 1;",
        "ensures result == p + 1; ensures pointer_origin(result, p + 1);",
    );
    let error = verify_c0_sources(&promised, &[("callback.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    verify_c0_sources(
        &promised.replace(
            "ensures result == &p->second + 1;",
            "ensures result == &p->first;",
        ),
        &[(
            "callback.c",
            c.replace("f(&p->first) + 1", "f(&p->first) - 1").as_str(),
        )],
    )
    .unwrap();
}

#[test]
fn inferred_member_returns_do_not_authenticate_callee_automatic_storage() {
    let c = "struct Pair { int32 first; int32 second; }; int32* leak(void) { struct Pair local; return &local.first; } int32 probe(int32* p) { int32* q = leak(); if (q == p) return *q; return 0; }";
    let proof = r#"verifying "local.c";
        int32* leak() { ensures result == result; } by { execute(); simp(); }
        int32 probe(int32* p) { views *p; ensures result == result; } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("local.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
}

#[test]
fn algebraic_pointer_fields_require_complete_origin_equality() {
    let c = "void probe(int32* p, int32* q) {}";
    let proof = r#"verifying "model.c";
        spec enum Ref { At(int32*) }
        void probe(int32* p, int32* q) {
            requires p == q;
            ensures Ref::At(p) == Ref::At(q);
        } by { execute(); simp(); }"#;
    assert!(verify_c0_sources(proof, &[("model.c", c)]).is_err());
    let promised = proof.replace(
        "requires p == q;",
        "requires p == q; requires pointer_origin(p, q);",
    );
    verify_c0_sources(&promised, &[("model.c", c)]).unwrap();
}

#[test]
fn caller_owned_pointer_cells_keep_domains_across_a_writing_helper() {
    let source = "struct Pair { int32 first; int32 second; }; struct Holder { int32* value; }; void touch(int32* tag) { *tag = 1; } int32 probe(struct Pair* p, struct Holder* h, int32* tag) { h->value = &p->first; touch(tag); return *(h->value + 1); }";
    let proof = r#"verifying "frame.c";
        void touch(int32* tag) { owns *tag; ensures *tag == 1; } by { execute(); simp(); }
        int32 probe(struct Pair* p, struct Holder* h, int32* tag) {
            owns h->value; owns *tag;
            views p->first; views p->second;
            requires separate(memory(h->value), memory(p->first));
            requires separate(memory(h->value), memory(p->second));
            requires separate(memory(*tag), memory(p->first));
            requires separate(memory(*tag), memory(p->second));
            ensures result == p->second;
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("frame.c", source)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    verify_c0_sources(
        &proof.replace(
            "ensures result == p->second;",
            "ensures result == p->first;",
        ),
        &[(
            "frame.c",
            source.replace("h->value + 1", "h->value + 0").as_str(),
        )],
    )
    .unwrap();
}

#[test]
fn checked_input_origin_chains_and_cycles_preserve_one_designation() {
    let c = "int32 probe(int32* p, int32* q, int32* r) { return *p; }";
    let proof = r#"verifying "chain.c";
        int32 probe(int32* p, int32* q, int32* r) {
            requires p == q; requires q == r;
            requires pointer_origin(p, q); requires pointer_origin(q, r);
            views *r; ensures result == *r;
        } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("chain.c", c)]).unwrap();
    let self_cycle = proof.replace("views *r;", "requires pointer_origin(r, r); views *r;");
    verify_c0_sources(&self_cycle, &[("chain.c", c)]).unwrap();
    let cycle = proof
        .replace("pointer_origin(q, r)", "pointer_origin(q, p)")
        .replace(
            "views *r; ensures result == *r;",
            "views *p; ensures result == *p;",
        );
    verify_c0_sources(&cycle, &[("chain.c", c)]).unwrap();
}

#[test]
fn derived_numeric_viewability_cannot_issue_an_input_domain() {
    let c = "struct Pair { int32 first; int32 second; }; void advance(int32* p, int32* q) { p = p + 1; } void probe(struct Pair* p) { advance(&p->first + 1, &p->second); }";
    let proof = r#"verifying "alias.c";
        void advance(int32* p, int32* q) {
            requires p == q; views *q; ensures true;
        } by {
            have viewable(p[0..1]) by { rewrite(p == q); simp(); }
            execute(); simp();
        }
        void probe(struct Pair* p) {
            views p->first; views p->second; ensures true;
        } by { execute(); simp(); }"#;
    let error = verify_c0_sources(proof, &[("alias.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
    let promised = proof
        .replace(
            "requires p == q;",
            "requires p == q; requires pointer_origin(p, q);",
        )
        .replace("have viewable(p[0..1]) by { rewrite(p == q); simp(); }", "");
    let valid = c.replace(
        "advance(&p->first + 1, &p->second)",
        "advance(&p->first, &p->first)",
    );
    verify_c0_sources(&promised, &[("alias.c", valid.as_str())]).unwrap();
    assert!(verify_c0_sources(&promised, &[("alias.c", c)]).is_err());
}

#[test]
fn symbolic_allocation_size_bounds_member_array_selection() {
    let c = "struct Record { int32 values[4]; }; int32 probe(uint64 bytes) { struct Record* p = malloc(bytes); if (p == 0) { return 0; } int32* end = p->values + 4; free(p); return 0; }";
    let proof = r#"verifying "heap.c";
        int32 probe(uint64 bytes) {
            requires bytes == 16u64;
            ensures result == 0;
        } by { execute(); simp(); }"#;
    verify_c0_sources(proof, &[("heap.c", c)]).unwrap();
    let error = verify_c0_sources(&proof.replace("16u64", "4u64"), &[("heap.c", c)]).unwrap_err();
    assert!(error.to_string().contains("undefined behavior"), "{error}");
}
