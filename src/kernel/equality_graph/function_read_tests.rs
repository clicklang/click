use super::*;

/// A function-pointer read is the cell's load, the same address base an
/// object-pointer read of the cell has (`design/loads.md`, "Terms"); the
/// function-pointer type is the decoding's.
fn function_read(memory: &SharedMemory, address: &OldAddress) -> OldAddress {
    OldAddress::loaded_value(memory, address)
}

fn callback_value(name: &str) -> ProgramValue {
    ProgramValue::typed_pointer(
        OldAddress::function(name),
        ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    )
}

/// A function-pointer read of the stored cell itself is answered by the
/// store, as an object-pointer read is: the memory records the value, so
/// the read-over-write authority relates them with no fact.
#[test]
fn a_function_pointer_read_of_its_stored_cell_is_the_stored_function() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = OldAddress {
        base: "callback-slot".into(),
        offset: AddressOffset::constant(0),
    };
    let target = OldAddress::function("callback");
    let memory =
        intern_memory(SymbolicMemory::new().store(slot.clone(), callback_value("callback")));
    let read = function_read(&memory, &slot);
    let empty = PureFactContext::new();
    assert!(empty.pointers_known_equal(&read, &target));
    let replacement = OldAddress::function("replacement");
    let after = intern_memory(
        memory
            .memory()
            .clone()
            .store(slot.clone(), callback_value("replacement")),
    );
    let new_read = function_read(&after, &slot);
    assert!(empty.pointers_known_equal(&new_read, &replacement));
    assert!(!empty.pointers_known_equal(&new_read, &target));
    assert!(empty.pointers_known_equal(&read, &target));
}

/// A read through an alias of the cell is not answered by the cell's cached
/// value: it needs the alias's address equality and the store's equation.
#[test]
fn a_function_pointer_read_through_an_alias_requires_explicit_store_equation() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = OldAddress {
        base: "callback-slot".into(),
        offset: AddressOffset::constant(0),
    };
    let target = OldAddress::function("callback");
    let stored = callback_value("callback");
    let memory = intern_memory(SymbolicMemory::new().store(slot.clone(), stored.clone()));
    let query = OldAddress::symbolic(Variable(992001));
    let read = function_read(&memory, &query);
    let empty = PureFactContext::new().assume_condition(
        OldConditionTerm::address_equal(slot.clone(), query.clone()),
        true,
    );
    assert!(
        !empty.pointers_known_equal(&read, &target),
        "cached value leaked"
    );
    let equation =
        crate::kernel::memory_history::store_value_equation(memory.memory(), &slot, &stored)
            .expect("function store equation");
    let facts = empty.clone().assume_proposition(equation.clone());
    assert!(facts.pointers_known_equal(&read, &target));
    let before_alias = PureFactContext::new().assume_proposition(equation);
    assert!(!before_alias.pointers_known_equal(&read, &target));
    let after_alias = before_alias.assume_condition(
        OldConditionTerm::address_equal(slot.clone(), query.clone()),
        true,
    );
    assert!(after_alias.pointers_known_equal(&read, &target));
    let replacement = callback_value("replacement");
    let after = intern_memory(
        memory
            .memory()
            .clone()
            .store(slot.clone(), replacement.clone()),
    );
    let new_read = function_read(&after, &query);
    assert!(!facts.pointers_known_equal(&new_read, &OldAddress::function("replacement")));
    let updated = facts.assume_proposition(
        crate::kernel::memory_history::store_value_equation(after.memory(), &slot, &replacement)
            .unwrap(),
    );
    assert!(updated.pointers_known_equal(&new_read, &OldAddress::function("replacement")));
    assert!(!updated.pointers_known_equal(&new_read, &target));
    assert!(updated.pointers_known_equal(&read, &target));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/function_read_tests.rs");
}
