use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/enumerate/enumerate.click");

/// `slice.iter().enumerate()` holds the slice iterator's state and the
/// count of values it has yielded: the index each iteration yields is that
/// count, and the element is read through the cursor.
#[test]
fn charon_enumerated_slice_loops_verify_from_their_count() {
    let p = Project::from_fixture("design/charon-trial/enumerate");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The index yielded is the count before the advance.
        (
            "        invariant iter_count != 0u64 implies last == iter_count - 1u64;\n",
            "        invariant iter_count != 0u64 implies last == iter_count;\n",
            "last_index",
        ),
        // The count starts at zero.
        (
            "        invariant iter_count == bytes.len() - iter_remaining;\n",
            "        invariant iter_count == (bytes.len() - iter_remaining) + 1u64;\n",
            "last_index",
        ),
        // A `u16` element is at most 65535.
        (
            "    ensures result <= 65535u32;\n",
            "    ensures result <= 65534u32;\n",
            "last_pair",
        ),
    ] {
        // Only the function that holds the change is verified again.
        let function = SIDECAR
            .split("\nfn ")
            .skip(1)
            .find(|function| function.contains(before))
            .unwrap_or_else(|| panic!("{before}"));
        let invalid = format!(
            "verifying \"enumerate.rs\";\nfn {}",
            function.replacen(before, after, 1)
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}
