use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/early-exits/exits.click");

/// A `return` from a loop body, from one loop or two deep and from a range
/// `for`, runs to the function exit, and a labeled `break` or `continue`
/// leaves every loop it crosses: each verifies from ordinary invariants.
#[test]
fn charon_loop_early_exits_verify() {
    let p = Project::from_fixture("design/charon-trial/early-exits");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The early `return true` needs a byte to read.
        (
            "    ensures result implies xs.len() != 0u64;\n",
            "    ensures result implies xs.len() == 0u64;\n",
            "has_zero",
        ),
        // The early `return i` returns a matching byte's index.
        (
            "    ensures result < xs.len() implies xs[result] == v;\n",
            "    ensures result < xs.len() implies xs[result] != v;\n",
            "position",
        ),
        // A labeled `break` leaves before `i` passes `n`, but `n` may be 0.
        (
            "fn first_hit(n: u32, m: u32) -> u32 {\n    ensures result <= n;\n",
            "fn first_hit(n: u32, m: u32) -> u32 {\n    ensures result < n;\n",
            "first_hit",
        ),
        // `continue 'rows` skips the store at `j == 2`, so the count is at
        // most 1, not 0.
        (
            "    ensures result <= m;\n",
            "    ensures result == 0u32;\n",
            "skip_rows",
        ),
    ] {
        // Only the function that holds the change is verified again.
        let function = SIDECAR
            .split("\nfn ")
            .skip(1)
            .find(|function| function.contains(before.trim_start_matches("fn ")))
            .unwrap_or_else(|| panic!("{before}"));
        let function = format!("fn {function}");
        assert!(function.contains(before), "{before}");
        let invalid = format!(
            "verifying \"exits.rs\";\n{}",
            function.replacen(before, after, 1)
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}
