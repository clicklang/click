use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/generic-traits/shapes.click");

// A generic crate trait's block states every instance's interface with its
// type parameter abstract; an instance's own block adds clauses at its
// type. Each implementation refines its instance's interface, and a call
// through a bound or `dyn` of an instance assumes it.
#[test]
fn charon_generic_trait_instances_refine_their_interfaces() {
    let p = Project::from_fixture("design/charon-trial/generic-traits");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The generic block binds every instance's implementation.
        (
            "        ensures result != x;\n    }\n}\n\n// The `i32`",
            "        ensures result != x;\n        ensures result == x + 1;\n    }\n}\n\n// The `i32`",
            "`<generic_traits::Wide as generic_traits::Scale<u32>>::scale.interface_ensures_1`",
        ),
        // The instance block binds only its instance's.
        (
            "        ensures x < result;\n    }\n}\n\ntrait generic_traits::Scale<u32>",
            "        ensures x + 1 < result;\n    }\n}\n\ntrait generic_traits::Scale<u32>",
            "`<generic_traits::Square as generic_traits::Scale<i32>>::scale.interface_ensures_1`",
        ),
        // A call through the `u32` instance knows the generic clauses and its
        // own, not the `i32` instance's.
        (
            "    requires x <= 1000;\n    ensures result != x;\n} by { execute(); simp(); }\n\nfn generic_traits::through_bound",
            "    requires x <= 1000;\n    ensures x < result;\n} by { execute(); simp(); }\n\nfn generic_traits::through_bound",
            "generic_traits::wide_total.ensures_0",
        ),
    ] {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a claim the interfaces do not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

const OBJECT_SIDECAR: &str =
    include_str!("../../design/charon-trial/generic-trait-objects/shapes.click");

// A generic crate trait's `function`s are each instance's object fields at
// the instance's types, `last(self) -> T` an `i32` field of `Bag<i32>`'s
// object and `items(self) -> List<T>` a `List<i32>` one. A struct packed as
// an instance's object has its implementation's definitions as the fields.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_generic_trait_objects_carry_state_at_each_instance() {
    let p = Project::from_fixture("design/charon-trial/generic-trait-objects");
    fs::write(p.root.join("borrow.click"), OBJECT_SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(OBJECT_SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The generic interface binds the implementation's memory.
        (
            "        ensures count(self) == old(count(self)) + 1;",
            "        ensures count(self) == old(count(self)) + 2;",
            "`<bags::Counter as bags::Bag<i32>>::insert.interface_ensures_0`",
        ),
        // A call through the instance knows the interface's fields only.
        (
            "    ensures result == old(count(bag)) + 1;\n    ensures last(bag) == x;\n} by { execute(); simp(); }\n\nfn bags::fill_dyn",
            "    ensures result == old(count(bag)) + 1;\n    ensures last(bag) == x + 1;\n} by { execute(); simp(); }\n\nfn bags::fill_dyn",
            "bags::fill.ensures_1",
        ),
        // The packed struct's fields follow its definitions.
        (
            "fn bags::through_dyn(x: i32) -> i32 {\n    ensures result == x;",
            "fn bags::through_dyn(x: i32) -> i32 {\n    ensures result == x + 1;",
            "bags::through_dyn.ensures_0",
        ),
        // An implementation defines a `List<T>` field at its instance.
        (
            "        List<i32>::Cons(self.value, List<i32>::Nil)",
            "        List<i32>::Nil",
            "`<bags::Slot as bags::Holder<i32>>::put.interface_ensures_0`",
        ),
    ] {
        assert!(OBJECT_SIDECAR.contains(before), "{before}");
        let invalid = OBJECT_SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a claim the object state does not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}
