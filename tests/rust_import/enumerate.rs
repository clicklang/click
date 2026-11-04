use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/enumerate/enumerate.click");

fn prepared_enumeration() -> click::languages::rust::PreparedRustImport {
    let p = Project::from_fixture("design/charon-trial/enumerate");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p.prepared().unwrap()
}

/// `slice.iter().enumerate()` is read through `iter.len()`: the index each
/// iteration yields is how far it has advanced, `len - iter.len()`, and the
/// element is the slice's there, with no cursor to state.
#[test]
fn charon_enumerated_slice_loops_verify_from_their_count() {
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared_enumeration())
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
    // The index yielded is how far the iterator stood before the advance.
    rejects_enumeration_mutation(
        "        invariant iter.len() != bytes.len() implies last == bytes.len() - iter.len() - 1u64;\n",
        "        invariant iter.len() != bytes.len() implies last == bytes.len() - iter.len();\n",
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
