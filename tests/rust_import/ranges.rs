use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/ranges/ranges.click");

/// A `for` over an integer range holds the range as its two bounds and
/// yields `start` while `start < end`; loops at every checked width, a slice
/// indexed by the loop variable, and nested ranges verify from invariants
/// over `iter_start` and `iter_end`.
#[test]
fn charon_range_loops_verify_from_their_bounds() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The count trails the yielded value, it does not lead it.
        (
            "        invariant total == iter_start;\n",
            "        invariant total == iter_start + 1u32;\n",
            "count_to",
        ),
        // The last iteration reads the final byte, not the first.
        (
            "    ensures bytes.len() != 0u64 implies result == bytes[bytes.len() - 1u64];\n",
            "    ensures bytes.len() != 0u64 implies result == bytes[0u64];\n",
            "last_byte",
        ),
        // Over a negative start the count can exceed `i32`.
        (
            "    requires 0i32 <= a and a <= b;\n",
            "    requires a <= b;\n",
            "signed overflow",
        ),
    ] {
        // Only the function that holds the change is verified again.
        let function = SIDECAR
            .split("\nfn ")
            .skip(1)
            .find(|function| function.contains(before))
            .unwrap_or_else(|| panic!("{before}"));
        let invalid = format!(
            "verifying \"ranges.rs\";\nfn {}",
            function.replacen(before, after, 1)
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}
