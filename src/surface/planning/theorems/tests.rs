use super::*;

const SHIFT: &str = "function shifted(x: Integer) -> Integer { x + 7 }";
const BOUND: &str = "theorem shifted_bound(x: Integer) { requires 0 <= x; ensures 7 <= shifted(x) by { unfold(shifted(x)); solve(); } }";

#[test]
fn single_theorem_discovery_expands_and_rechecks() {
    let proof = "by { solve() using { 0 <= value; }; }";
    let source = format!(
        "{SHIFT} theorem too_strong(x: Integer) {{ requires 100 <= x; ensures 7 <= shifted(x) by {{ unfold(shifted(x)); solve(); }} }} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) {proof} }}"
    );
    let verified = verify_click_theorems(&source).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified.last().unwrap().expanded_proof_source().unwrap();
    assert!(
        expanded.contains("apply(shifted_bound(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("solve("), "{expanded}");
    // The library declarations' proofs still contain solve; recheck only the
    // expanded target with those declarations supplied as dependencies.
    let expanded_source = source.replace(proof, &expanded);
    let file = parser::parse(&expanded_source).unwrap();
    let definitions = file.theorem_definitions();
    let functions = ClickFunctionEnvironment::new(file.click_function_definitions());
    crate::surface::without_implicit_solve(|| {
        crate::surface::proof::verify_theorem_definition(
            definitions.last().unwrap(),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &functions),
            &TheoremEnvironment::new(&definitions[..definitions.len() - 1]),
            None,
        )
    })
    .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn single_theorem_discovery_keeps_unlisted_facts_unavailable() {
    for premises in ["", "1 <= value;"] {
        let source = format!(
            "{SHIFT} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; requires 1 <= value; ensures 7 <= shifted(value) by {{ solve() using {{ {premises} }}; }} }}"
        );
        assert!(verify_click_theorems(&source).is_err(), "{source}");
    }
    let source = format!(
        "{SHIFT} {BOUND} theorem test(value: Integer) {{ requires 0 <= value; ensures 8 <= shifted(value) by {{ solve() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&source).is_err());
}

#[test]
fn single_theorem_discovery_does_not_invent_arguments_or_chain() {
    let hidden = format!(
        "{SHIFT} theorem hidden(x: Integer, witness: Integer) {{ requires 0 <= witness; requires x == witness; ensures 7 <= shifted(x) by {{ unfold(shifted(x)); solve(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ solve() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&hidden).is_err());
    let chain = format!(
        "{SHIFT} function middle(x: Integer) -> Integer {{ x }} theorem first(x: Integer) {{ requires 0 <= x; ensures 0 <= middle(x) by {{ unfold(middle(x)); solve(); }} }} theorem second(x: Integer) {{ requires 0 <= middle(x); ensures 7 <= shifted(x) by {{ unfold(middle(x)); unfold(shifted(x)); solve(); }} }} theorem test(value: Integer) {{ requires 0 <= value; ensures 7 <= shifted(value) by {{ solve() using {{ 0 <= value; }}; }} }}"
    );
    assert!(verify_click_theorems(&chain).is_err());
}

#[test]
fn single_theorem_discovery_finds_generic_library_law() {
    let proof = "by { solve() using {}; }";
    let source = format!(
        "import click::list; theorem test(xs: List<Integer>, ys: List<Integer>) {{ ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) {proof} }}"
    );
    let verified = verify_click_theorems(&source).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("length_append"), "{expanded}");
    assert!(!expanded.contains("solve("), "{expanded}");
    verify_click_theorems(&source.replace(proof, &expanded))
        .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn single_theorem_discovery_closes_c_outcome_and_expands() {
    let proof = "by { step_until(function.exit); solve() using { 0 <= to_integer(x); }; }";
    let source = format!(
        "verifying \"noop.c\"; {SHIFT} {BOUND} void noop(int32 x) {{ requires 0 <= to_integer(x); ensures 7 <= shifted(to_integer(x)); }} {proof}"
    );
    let c = [("noop.c", "void noop(int32 x) {}")];
    let verified = verify_c_sources(&source, &c).unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded = verified[0].expanded_proof_source().unwrap();
    assert!(expanded.contains("shifted_bound"), "{expanded}");
    assert!(!expanded.contains("solve("), "{expanded}");
    verify_c_sources(&source.replace(proof, &expanded), &c)
        .unwrap_or_else(|e| panic!("{expanded}: {}", e.report()));
}

#[test]
fn discovery_respects_library_imports_and_prefixes() {
    let file = parser::parse(
        "import click::integer; theorem probe(a: Integer, b: Integer) { ensures a < b; }",
    )
    .unwrap();
    let empty = parser::parse("").unwrap();
    let Ensure::Proposition(goal) = file.theorem_definitions()[0].ensures()[0].ensure() else {
        panic!()
    };
    let law = "click::integer::le_ne_lt";
    let visible = TheoremEnvironment::with_standard_library(&[])
        .unwrap()
        .with_discovery_library(&file)
        .unwrap();
    assert!(
        visible
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let hidden = TheoremEnvironment::with_standard_library(&[])
        .unwrap()
        .with_discovery_library(&empty)
        .unwrap();
    assert!(
        !hidden
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let position = *visible.standard_library_index.get(law).unwrap();
    let prefix = TheoremEnvironment::with_full_library_prefix(position, &[]).unwrap();
    assert!(
        !prefix
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let selected_prefix = prefix.with_discovery_library(&file).unwrap();
    assert!(
        !selected_prefix
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
    let through_law = TheoremEnvironment::with_full_library_prefix(position + 1, &[])
        .unwrap()
        .with_discovery_library(&file)
        .unwrap();
    assert!(
        through_law
            .conclusion_candidates(goal)
            .any(|candidate| candidate.name == law)
    );
}
