use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/impl-fn/closure.click");

fn impl_fn_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/impl-fn");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// An `impl Fn` or `<F: Fn>` parameter is a callable value as `&dyn Fn` is.
// A closure passed for it carries its contract fixed to its captures, a
// capture-free closure and a function item are their functions' addresses,
// and a callee's contract requirement is answered by refinement.
#[test]
#[ignore = "nightly: 5.9s in the parallel gate"]
fn charon_impl_fn_arguments_meet_named_contracts() {
    let p = impl_fn_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // A capturing closure's contract weaker than the one required.
        (
            "    ensures result == y + k;\n} by { execute(); simp(); }\n\nfn impl_fn::caller(",
            "    ensures result >= y;\n} by { execute(); simp(); }\n\nfn impl_fn::caller(",
            "precondition clause 1 of",
        ),
        // A function item passed for `impl Fn` that does not meet its contract.
        (
            "fn impl_fn::inc(y: i32) -> i32 {\n    requires 0 <= y and y <= 2000;\n    ensures result == y + 1;",
            "fn impl_fn::inc(y: i32) -> i32 {\n    requires 0 <= y and y <= 2000;\n    ensures result >= y;",
            "does not satisfy named contract `Increments`",
        ),
        // A call through a callable with no contract.
        (
            "    requires Increments(g);\n",
            "",
            "cannot verify call through function pointer",
        ),
        // A false closure contract.
        (
            "    ensures result == y + k;\n} by { execute(); simp(); }\n\nfn impl_fn::twice::{closure#1}",
            "    ensures result == y + k + 1;\n} by { execute(); simp(); }\n\nfn impl_fn::twice::{closure#1}",
            "ensures_1",
        ),
        // A type parameter's bound must be the source's.
        (
            "fn impl_fn::apply<F: Fn(i32) -> i32>(f: F,",
            "fn impl_fn::apply<F: Fn(i32) -> u32>(f: F,",
            "contract `Increments` expects int32 (*)(int32), got uint32 (*)(int32)",
        ),
    ] {
        let invalid = SIDECAR.replacen(before, after, 1);
        assert_ne!(invalid, SIDECAR, "{before}");
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a callable without the contract its use needs must fail");
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 11.9s in the parallel gate"]
fn charon_impl_fn_tools_recheck_expanded_certificates() {
    let p = impl_fn_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I7_impl_fn_I5_apply.contract",
        "__rust_q_I7_impl_fn_I5_named.contract",
        "__rust_q_I7_impl_fn_I5_twice.contract",
        "__rust_q_I7_impl_fn_I4_both.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}
