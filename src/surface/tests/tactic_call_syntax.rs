use super::*;

#[test]
fn smart_proof_calls_have_identical_meaning_with_optional_braces() {
    for tactic in ["solve", "assumption", "normalize"] {
        let call = format!("by {tactic}();");
        let block = format!("by {{ {tactic}(); }}");
        let source = |proof: &str| {
            format!(
                "verifying \"identity.c\"; int32 identity(int32 x) {{ ensures result == x {proof} }}"
            )
        };
        assert_eq!(
            parser::parse(&source(&call)).unwrap().function_blocks(),
            parser::parse(&source(&block)).unwrap().function_blocks(),
            "{tactic}: braces must only delimit the same one-tactic proof"
        );
        let goal = if tactic == "normalize" {
            "7 == 7"
        } else {
            "x == 7"
        };
        for proof in [&call, &block] {
            verify_click_theorems(&format!(
                "theorem fact(x: int32) {{ requires x == 7; ensures {goal} {proof} }}"
            ))
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"));
        }
    }
}

#[test]
fn bare_smart_tactics_are_rejected_in_proofs_and_scripts() {
    for proof in [
        "by solve;",
        "by { solve; }",
        "by { have x == 7 by assumption(); solve; }",
        "by { have x == 7 by solve; assumption(); }",
        "by solve using { x == 7; };",
    ] {
        let source =
            format!("theorem fact(x: int32) {{ requires x == 7; ensures x == 7 {proof} }}");
        let error = parser::parse(&source).expect_err(proof);
        assert!(
            error.message().contains("requires parentheses"),
            "{proof}: {error:?}"
        );
    }
    for proof in ["by solve(1);", "by { solve(1); }"] {
        let error =
            parser::parse(&format!("theorem fact() {{ ensures true {proof} }}")).unwrap_err();
        assert!(
            error.message().contains("no arguments"),
            "{proof}: {error:?}"
        );
    }
}

#[test]
fn nested_single_tactic_calls_keep_their_checked_scopes() {
    verify_click_theorems(
        "theorem fact(x: int32) {
        requires x == 7;
        ensures x == 7 by {
            have first: x == 7;
            have second: x == 7 by { solve(); }
            have x == 7 by assumption();
            solve() using { first; second; };
        }
    }",
    )
    .unwrap();
}

#[test]
fn whole_proof_auto_call_cannot_be_shadowed_by_a_user_tactic() {
    let error = parser::parse("tactic solve() { ensures true; } by solve();").unwrap_err();
    assert!(error.message().contains("built-in"), "{error:?}");
}

#[test]
fn invariant_closer_requires_a_call_head_with_optional_single_body_braces() {
    for body in ["assumption();", "{ assumption(); }"] {
        let source = format!(
            r#"verifying "test.c"; int32 fact() {{ ensures true by {{ close_invariants() by {body} }} }}"#
        );
        let parsed = parser::parse(&source).unwrap();
        let printed = super::super::printing::format_partial_tactic_sequence(
            parsed.function_blocks()[0].ensures()[0]
                .proof()
                .tactics()
                .unwrap(),
        );
        assert!(printed.starts_with("close_invariants() by {"), "{printed}");
        assert!(!printed.ends_with(';'));
        let error = parser::parse(&source.replace("close_invariants()", "close_invariants"))
            .expect_err("the old bare head is refused");
        assert!(
            error.message().contains("requires parentheses"),
            "{error:?}"
        );
    }
}

#[test]
fn canonical_using_calls_wrap_long_premises_and_keep_their_terminator() {
    let left = "first_parameter_with_a_descriptive_mathematical_name";
    let right = "second_parameter_with_a_descriptive_mathematical_name";
    let head = format!(
        "theorem equal({left}: Integer, {right}: Integer) {{ requires {left} == {right}; ensures {left} == {right}"
    );
    let source = format!("{head} by {{ solve() using {{ {left} == {right}; }} }} }}");
    verify_click_theorems(&source).unwrap();
    let parsed = parser::parse(&source).unwrap();
    let proof = parsed.theorem_definitions()[0].ensures()[0].proof();
    let printed = super::super::printing::format_partial_tactic_sequence(proof.tactics().unwrap());
    assert!(printed.ends_with("};"), "{printed}");
    assert!(printed.lines().all(|line| line.len() <= 100), "{printed}");
    assert!(printed.contains("\n        "), "{printed}");
    let rewritten = format!("{head} by {{ {printed} }} }}");
    let reparsed = parser::parse(&rewritten).unwrap();
    assert_eq!(
        proof,
        reparsed.theorem_definitions()[0].ensures()[0].proof()
    );
    verify_click_theorems(&rewritten).unwrap();
}

#[test]
fn binary_splits_require_then_exactly_when_they_have_an_interface() {
    let source = |body: &str| {
        format!("verifying \"split.c\"; int32 split(int32 x) {{ ensures true by {{ {body} }} }}")
    };
    for head in ["if x == 0", "branch"] {
        for interface in ["", "ensuring { fact x == x; } then "] {
            let written = source(&format!(
                "{head} {interface}{{ assumption(); }} else {{ assumption(); }}"
            ));
            let parsed = parser::parse(&written).unwrap();
            let proof = parsed.function_blocks()[0].ensures()[0].proof();
            let printed =
                super::super::printing::format_partial_tactic_sequence(proof.tactics().unwrap());
            assert_eq!(
                printed.contains("then {"),
                !interface.is_empty(),
                "{printed}"
            );
            let reparsed = parser::parse(&source(&printed)).unwrap();
            assert_eq!(proof, reparsed.function_blocks()[0].ensures()[0].proof());
        }
        let error = parser::parse(&source(&format!(
            "{head} then {{ assumption(); }} else {{ assumption(); }}"
        )))
        .unwrap_err();
        assert!(
            error.message().contains("requires an `ensuring` interface"),
            "{error:?}"
        );
        let error = parser::parse(&source(&format!(
            "{head} ensuring {{ fact x == x; }} {{ assumption(); }} else {{ assumption(); }}"
        )))
        .unwrap_err();
        assert!(error.message().contains("then"), "{error:?}");
    }
}

/// `simp`, `auto`, `arithmetic` and `execute_until` are removed spellings:
/// in each place a tactic or a one-tactic proof stands, the parser refuses
/// them and names what replaced them.
#[test]
fn removed_tactic_spellings_name_their_replacement() {
    for (proof, replacement) in [
        ("by simp();", "`solve()`"),
        ("by { simp(); }", "`solve()`"),
        ("by { normalize(); simp() using { x == 7; }; }", "`solve()`"),
        ("by auto();", "the omitted proof"),
        ("by { auto(); }", "the omitted proof"),
        (
            "by { have x == 7 by auto(); assumption(); }",
            "the omitted proof",
        ),
        ("by arithmetic();", "`solve() using {}`"),
        (
            "by { arithmetic() using { x == 7; }; }",
            "`solve() using { ... }`",
        ),
        ("by { execute_until(function.exit); }", "`step_until`"),
    ] {
        let source =
            format!("theorem fact(x: int32) {{ requires x == 7; ensures x == 7 {proof} }}");
        let error = parser::parse(&source).expect_err(proof);
        assert!(error.message().contains(replacement), "{proof}: {error:?}");
    }
}
