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
            "        ensures result != x;\n        ensures result == x;\n    }\n}\n\n// The `i32`",
            "the trait method interface `generic_traits::Scale<u32>::scale`",
        ),
        // It is checked once for every type: a value of an abstract type has
        // equality only, so arithmetic belongs in an instance's block.
        (
            "        ensures result != x;\n    }\n}\n\n// The `i32`",
            "        ensures result != x;\n        ensures result == x + 1;\n    }\n}\n\n// The `i32`",
            "the generic interface `generic_traits::Scale<T>::scale` does not mean something at every type",
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
    // Keep the original full positive check. Select complete function
    // proofs for local failures; declaration/interface boundary cases
    // retain their original whole-module checks.
    for (head, before, after, expected) in [
        // The generic interface binds the implementation's memory.
        (
            Some("fn insert(&mut self, x: i32)"),
            "        ensures count(self) == old(count(self)) + 1;",
            "        ensures count(self) == old(count(self)) + 2;",
            "`<bags::Counter as bags::Bag<i32>>::insert.interface_ensures_0`",
        ),
        // A call through the instance knows the interface's fields only.
        (
            Some("fn bags::fill<"),
            "    ensures result == old(count(bag)) + 1;\n    ensures last(bag) == x;\n} by { execute(); simp(); }\n\nfn bags::fill_dyn",
            "    ensures result == old(count(bag)) + 1;\n    ensures last(bag) == x + 1;\n} by { execute(); simp(); }\n\nfn bags::fill_dyn",
            "bags::fill.ensures_1",
        ),
        // The packed struct's fields follow its definitions.
        (
            Some("fn bags::through_dyn("),
            "fn bags::through_dyn(x: i32) -> i32 {\n    ensures result == x;",
            "fn bags::through_dyn(x: i32) -> i32 {\n    ensures result == x + 1;",
            "bags::through_dyn.ensures_0",
        ),
        // An implementation defines a `List<T>` field at its instance.
        (
            Some("fn put(&mut self, x: i32)"),
            "        List<i32>::Cons(self.value, List<i32>::Nil)",
            "        List<i32>::Nil",
            "`<bags::Slot as bags::Holder<i32>>::put.interface_ensures_0`",
        ),
    ] {
        assert!(OBJECT_SIDECAR.contains(before), "{before}");
        let invalid = OBJECT_SIDECAR.replacen(before, after, 1);
        let error = if let Some(head) = head {
            verify_rust_proof_after(&invalid, &prepared, head)
                .expect_err("a claim the object state does not justify must fail")
        } else {
            C0VerificationSession::new_program_prepared(&invalid, &prepared)
                .err()
                .expect("a claim the object state does not justify must fail")
        };
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

const IMPL_SIDECAR: &str = include_str!("../../design/charon-trial/generic-impls/shapes.click");

// A generic implementation, `impl<T> Keep<T> for Echo`, and a generic
// function, `pick<T: Copy>`, are each verified once with `T` an abstract
// type. A call at a scalar type calls that instance, whose contract is the
// generic one at its types.
#[test]
fn charon_generic_implementations_are_verified_once_for_every_type() {
    let p = Project::from_fixture("design/charon-trial/generic-impls");
    fs::write(p.root.join("borrow.click"), IMPL_SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(IMPL_SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // The generic implementation answers to the generic interface.
        (
            "        ensures result == x;\n    }\n}\n\n// One",
            "        ensures result != x;\n    }\n}\n\n// One",
            "<generic_impls::Echo as generic_impls::Keep<T>>::keep.interface_ensures_0",
        ),
        // The generic function's body is checked once for every type.
        (
            "    ensures not first implies result == b;",
            "    ensures result == a;",
            "generic_impls::pick.ensures_1",
        ),
        // A caller at `u32` knows the instance's contract and no more.
        (
            "fn generic_impls::through_wide(x: u32) -> u32 {\n    ensures result == x;",
            "fn generic_impls::through_wide(x: u32) -> u32 {\n    ensures result == x + 1;",
            "generic_impls::through_wide.ensures_0",
        ),
        (
            "    ensures result == y;",
            "    ensures result == x;",
            "generic_impls::choose.ensures_0",
        ),
    ] {
        assert!(IMPL_SIDECAR.contains(before), "{before}");
        let invalid = IMPL_SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a claim the generic contracts do not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

const STRUCT_SIDECAR: &str = include_str!("../../design/charon-trial/generic-structs/cells.click");

// A generic struct's fields of `T` are values of `T` in memory: generic
// functions over `&Cell<T>` and `&mut Pair<T>`, and the struct's own
// methods, are verified once with `T` abstract, and calls at `i32`, `u8` and
// `u32` use their contracts at the instances' own layouts.
#[test]
fn charon_generic_struct_fields_are_verified_once_for_every_type() {
    let p = Project::from_fixture("design/charon-trial/generic-structs");
    fs::write(p.root.join("borrow.click"), STRUCT_SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(STRUCT_SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // Two fields of `T` are two values.
        (
            "    ensures pair.first == old(pair.second);",
            "    ensures pair.first == old(pair.first);",
            "generic_structs::swap.ensures_0",
        ),
        // A caller at `u8` knows the instance's contract and no more.
        (
            "    ensures result == y;",
            "    ensures result == x;",
            "generic_structs::swapped.ensures_0",
        ),
        // A stored value of `T` reads back as itself, and only as itself:
        // a generic struct's method is verified once.
        (
            "        ensures result == self.value;",
            "        ensures result != self.value;",
            "generic_structs::Cell<T>::get.ensures_0",
        ),
        // Generic code's calls of generic code at its own `U` have their
        // contracts at `U`.
        (
            "        ensures result == self.value;\n    } by { execute(); simp(); }\n\n    fn set",
            "        ensures true;\n    } by { execute(); simp(); }\n\n    fn set",
            "generic_structs::read_twice.ensures_0",
        ),
        (
            "fn generic_structs::via_methods(x: u32) -> u32 {\n    ensures result == x;",
            "fn generic_structs::via_methods(x: u32) -> u32 {\n    ensures result == 0;",
            "generic_structs::via_methods.ensures_0",
        ),
    ] {
        assert!(STRUCT_SIDECAR.contains(before), "{before}");
        let invalid = STRUCT_SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a claim the generic contracts do not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

const REFERENCE_SIDECAR: &str = include_str!("../../design/charon-trial/generic-refs/refs.click");

// A reference to a value of `T`, `&T` or `&mut T`, reads and writes one value
// of `T` in memory: generic functions over them are verified once, and calls
// at `u32` pass references to struct fields.
#[test]
fn charon_references_to_type_parameter_values_are_verified_once() {
    let p = Project::from_fixture("design/charon-trial/generic-refs");
    fs::write(p.root.join("borrow.click"), REFERENCE_SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(REFERENCE_SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // Two references to `T` are two places.
        (
            "    ensures *left == old(*right);",
            "    ensures *left == old(*left);",
            "generic_refs::exchange.ensures_0",
        ),
        // A caller at `u32` owns what it lends as `&mut u32`. (A false
        // `ensures` here is rejected too, but slowly:
        // bugs/rust-auto-slow-to-reject-after-field-reference-calls.md.)
        (
            "    owns slots.a;\n    owns slots.b;\n    ensures result",
            "    owns slots.a;\n    views slots.b;\n    ensures result",
            "generic_refs::use_refs",
        ),
    ] {
        assert!(REFERENCE_SIDECAR.contains(before), "{before}");
        let invalid = REFERENCE_SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a claim the generic contracts do not justify must fail");
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::rust::names::display_rust_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}
