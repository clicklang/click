use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/ranges/ranges.click");

/// A `for` over an integer range holds the range as its two bounds and
/// yields `start` while `start < end`; loops at every checked width, a slice
/// indexed by the loop variable, and nested ranges verify from invariants
/// over the range's fields, `iter.start` and `iter.end`.
#[test]
fn charon_range_loops_verify_from_their_bounds() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    let witness = r#"fn grid(n: u32, m: u32) -> u32 {
    requires n == 2u32 and m == 3u32;
    ensures result == 6u32;
} by {
    step_until(function.exit);
}"#;
    let gate = with_rust_fixture_contract(SIDECAR, "grid", witness);
    ProgramVerificationSession::new_program_prepared(&gate, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The count trails the yielded value, it does not lead it.
        (
            "        invariant total == iter.start;\n",
            "        invariant total == iter.start + 1u32;\n",
            "count_to",
        ),
        // The last iteration reads the final byte, not the first.
        (
            "    ensures bytes.len() != 0u64 implies result == bytes[bytes.len() - 1u64];\n",
            "    ensures bytes.len() != 0u64 implies result == bytes[0u64];\n",
            "last_byte",
        ),
        // The count starts at zero, so it trails the yielded value by `a`.
        (
            "        invariant count == iter.start - a;\n",
            "        invariant count == iter.start;\n",
            "span",
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
        let error = ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}

/// A range loop's `next` binds the loop variable itself: the `Option` MIR
/// returns, and the temporary that holds it, are gone from every loop.
#[test]
fn charon_range_loops_bind_their_variable_without_an_option() {
    use click::languages::rust::schema::MirStatement;
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    let mut nexts = 0;
    for function in &prepared.export().functions {
        let Some(mir) = &function.mir else { continue };
        for statement in mir.blocks.iter().flat_map(|block| &block.statements) {
            if let MirStatement::RangeNext {
                option,
                payload,
                taken,
                ..
            } = statement
            {
                nexts += 1;
                assert_eq!(option, &None, "{}: {statement:?}", function.name);
                assert_eq!(
                    payload.is_some(),
                    *taken == Some(true),
                    "{}: {statement:?}",
                    function.name
                );
            }
        }
    }
    assert!(nexts > 0);
}

/// A range loop's failures name its iterator as the proof does, `iter.end`
/// inside the loop and `loop(0).iter.start` after it, and its points by the
/// `for` statement: no compiler temporary or bare region index appears.
#[test]
fn charon_range_loop_failures_name_the_iterator_as_the_proof_does() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    let failure = |before: &str, after: &str| {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        let error = verify_rust_function(&invalid, &prepared, "count_to")
            .expect_err("a false claim about the loop fails");
        click::languages::rust::names::display_rust_names(&format!("{error}")).into_owned()
    };
    // A false invariant fails at the loop's entry, naming the range's end.
    let entry = failure(
        "        invariant total == iter.start;\n",
        "        invariant total == iter.start + 1u32;\n",
    );
    assert!(entry.contains("iter.end"), "{entry}");
    // Without the bound, the exit is not pinned, and the facts there name
    // the range's start after the loop.
    let exit = failure(
        "        invariant iter.start <= n;\n        invariant total == iter.start;\n",
        "        invariant total == iter.start;\n",
    );
    assert!(exit.contains("loop(0).iter.start"), "{exit}");
    for rendered in [&entry, &exit] {
        assert!(!rendered.contains("__rust_mir"), "{rendered}");
        assert!(!rendered.contains("at(region("), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: symbolic nested range proof took 5.3s in the focused gate profile"]
fn charon_nested_range_grid_verifies_symbolically() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    verify_rust_function(SIDECAR, &prepared, "grid").unwrap_or_else(|error| panic!("{error:?}"));
}
