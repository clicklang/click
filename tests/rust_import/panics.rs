use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/panics/panics.click");

/// A Rust panic, `assert!`, `panic!`, `unreachable!`, `unwrap` or
/// `expect`, is an obligation that the call never reaches it: each verifies
/// under the precondition that rules it out, and without it the refusal
/// names the panic by its message.
#[test]
fn charon_panics_are_obligations() {
    let p = Project::from_fixture("design/charon-trial/panics");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, expected) in [
        (
            "fn above_three(x: u32) -> u32 {\n    requires x > 3;\n",
            "Rust panic `assertion failed: x > 3`",
        ),
        (
            "fn with_message(x: u32) -> u32 {\n    requires x > 3;\n",
            "Rust panic `too small`",
        ),
        (
            "fn formatted(x: u32) -> u32 {\n    requires x > 3;\n",
            "Rust panic `formatted message`",
        ),
        (
            "fn nonzero(x: u32) -> u32 {\n    requires x != 0;\n",
            "Rust panic `zero`",
        ),
        (
            "fn classify(x: u8) -> u8 {\n    requires x <= 1u8;\n",
            "Rust panic `internal error: entered unreachable code`",
        ),
        (
            "fn unwrapped(o: Option<u32>) -> u32 {\n    requires o != Option<u32>::None;\n",
            "precondition clause 1",
        ),
    ] {
        let function = SIDECAR
            .split("\nfn ")
            .skip(1)
            .map(|function| format!("fn {function}"))
            .find(|function| function.starts_with(before))
            .unwrap_or_else(|| panic!("{before}"));
        let (header, _) = before.split_once('\n').unwrap();
        let invalid = format!(
            "verifying \"panics.rs\";\n{}",
            function.replacen(before, &format!("{header}\n"), 1)
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` without its requirement must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}

/// A refused `assert!` names its condition, with the polarity under which
/// the call continues: `x != 0` for a panic when `x == 0`, and
/// `xs.len() > 0` for `assert!(xs.len() > 0)`, whose comparison the kernel
/// records as `xs.len() <= 0` being false.
#[test]
fn charon_refused_panic_names_its_condition() {
    let p = Project::from_fixture("design/charon-trial/panics");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    for (function, goal) in [
        (
            "fn nonzero(x: u32) -> u32 { ensures result == x; }",
            "could not show `x != 0u32`",
        ),
        (
            "fn first(xs: &[u8]) -> u8 { views *xs; ensures result == xs[0]; }",
            "could not show `xs.len() > 0u64`",
        ),
    ] {
        let invalid = format!("verifying \"panics.rs\";\n{function}\n");
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{function}` must fail"));
        let rendered = error.to_string();
        assert!(rendered.contains(goal), "{goal}: {rendered}");
    }
}
