use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/enumerate/enumerate.click");

fn prepared_enumeration() -> click::languages::rust::PreparedRustImport {
    let p = Project::from_fixture("design/charon-trial/enumerate");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p.prepared().unwrap()
}

/// `slice.iter().enumerate()` is `core`'s `Enumerate { iter, count }`: the
/// index each iteration yields is `iter.count`, and the element is the one
/// at `iter.as_slice()`.
#[test]
fn charon_enumerated_slice_loops_verify_from_their_count() {
    ProgramVerificationSession::new_program_prepared(SIDECAR, prepared_enumeration())
        .unwrap_or_else(|error| panic!("{error:?}"));
}

fn rejects_enumeration_mutation(before: &str, after: &str, function: &str) {
    assert!(SIDECAR.contains(before), "{before}");
    let invalid = SIDECAR.replacen(before, after, 1);
    // The positive test checks the complete fixture. Each mutation checks
    // only its changed function, retaining the other contracts as interfaces.
    let error = verify_rust_function(&invalid, &prepared_enumeration(), function)
        .err()
        .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
    assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
    let rendered = format!("{error:?} {error}");
    assert!(rendered.contains(function), "{function}: {rendered}");
}

#[test]
fn charon_enumeration_rejects_shifted_yielded_index() {
    // The index yielded is the count before the element is counted.
    rejects_enumeration_mutation(
        "        invariant iter.count != 0u64 implies last == iter.count - 1u64;\n",
        "        invariant iter.count != 0u64 implies last == iter.count;\n",
        "last_index",
    );
}

#[test]
fn charon_enumeration_rejects_an_advance_before_the_first_pass() {
    // The enumerated iterator starts with every element left.
    rejects_enumeration_mutation(
        "        invariant iter.len() <= bytes.len();\n",
        "        invariant iter.len() < bytes.len();\n",
        "last_index",
    );
}

#[test]
fn charon_enumeration_rejects_understated_element_bound() {
    // A `u16` element can be 65535.
    rejects_enumeration_mutation(
        "    ensures result <= 65535u32;\n",
        "    ensures result <= 65534u32;\n",
        "last_pair",
    );
}

/// An enumerated loop's `next` binds the index and the element itself: the
/// `Option` MIR returns, its tag test and its temporary are gone.
#[test]
fn charon_enumerated_loops_bind_their_index_and_element_without_an_option() {
    use click::languages::rust::schema::{MirStatement, Type};
    let prepared = prepared_enumeration();
    let mut bound = 0;
    for function in &prepared.export().functions {
        let Some(mir) = &function.mir else { continue };
        assert!(
            !mir.locals
                .iter()
                .any(|local| matches!(local.value_type, Type::EnumerateOption { .. })),
            "{}",
            function.name
        );
        for statement in mir.blocks.iter().flat_map(|block| &block.statements) {
            if let MirStatement::EnumerateNext {
                option,
                index,
                element,
                taken,
                ..
            } = statement
            {
                assert_eq!(option, &None, "{}: {statement:?}", function.name);
                assert!(
                    (index.is_none() && element.is_none()) || *taken == Some(true),
                    "{}: {statement:?}",
                    function.name
                );
                bound += usize::from(index.is_some() || element.is_some());
            }
        }
    }
    assert!(bound > 0);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: expand and replay an enumerated slice proof"]
fn charon_enumerated_slice_count_expands_and_replays() {
    let prepared = prepared_enumeration();
    let claim = "last_index.contract";
    let expanded =
        click::surface::expand_program_prepared_claim_source_by_label(SIDECAR, &prepared, claim)
            .unwrap();
    assert_ne!(expanded, SIDECAR);
    assert!(!expanded.contains("<enumeration count>"), "{expanded}");
    assert!(!expanded.contains("_count"), "{expanded}");
    click::surface::without_implicit_solve_for_claim(claim, || {
        ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
            .map(|_| ())
            .map_err(|error| error.to_string())
    })
    .unwrap();
}
