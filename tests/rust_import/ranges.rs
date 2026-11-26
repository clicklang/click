use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/ranges/ranges.click");

/// A `for` over an integer range holds the range as its two bounds and
/// yields `start` while `start < end`; loops at every checked width, a slice
/// indexed by the loop variable, and nested ranges verify from invariants
/// over the range's fields, `iter.start` and `iter.end`.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 9.3s in the parallel gate"]
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
    reject_range_mutations(
        &prepared,
        &[
            // The count trails the yielded value, it does not lead it.
            (
                "        invariant total == iter.start;\n",
                "        invariant total == iter.start + 1u32;\n",
                "count_to",
            ),
        ],
    );
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: additional range last-element and nonzero-start mutations"]
fn charon_range_loops_refuse_additional_mutations() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    reject_range_mutations(
        &prepared,
        &[
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
        ],
    );
}

fn reject_range_mutations(
    prepared: &click::languages::rust::PreparedRustImport,
    cases: &[(&str, &str, &str)],
) {
    for &(before, after, expected) in cases {
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
        let error = ProgramVerificationSession::new_program_prepared(&invalid, prepared)
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
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
    // The entry value of the bound equals the parameter. The error still
    // names the accessor from the invariant the proof actually wrote.
    let entry = failure(
        "        invariant iter.end == n;\n",
        "        invariant iter.end != n;\n",
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: symbolic nested range proof took 5.3s in the focused gate profile"]
fn charon_nested_range_grid_verifies_symbolically() {
    let p = Project::from_fixture("design/charon-trial/ranges");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    verify_rust_function(SIDECAR, &prepared, "grid").unwrap_or_else(|error| panic!("{error:?}"));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: expand and replay both range iterator forms"]
fn charon_range_bounds_expand_and_replay() {
    for (fixture, sidecar, claim) in [
        ("ranges", SIDECAR, "count_to.contract"),
        (
            "inclusive-ranges",
            include_str!("../../design/charon-trial/inclusive-ranges/inclusive.click"),
            "count_through.contract",
        ),
    ] {
        let p = Project::from_fixture(&format!("design/charon-trial/{fixture}"));
        fs::write(p.root.join("borrow.click"), sidecar).unwrap();
        let prepared = p.prepared().unwrap();
        let expanded = click::surface::expand_program_prepared_claim_source_by_label(
            sidecar, &prepared, claim,
        )
        .unwrap_or_else(|error| panic!("{claim}: {error}"));
        assert_ne!(expanded, sidecar);
        assert!(!expanded.contains("__rust_mir"), "{expanded}");
        assert!(!expanded.contains("<range "), "{expanded}");
        click::surface::without_implicit_solve_for_claim(claim, || {
            ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
                .map(|_| ())
                .map_err(|error| error.to_string())
        })
        .unwrap_or_else(|error| panic!("{claim}: {error}\n{expanded}"));
    }
}
