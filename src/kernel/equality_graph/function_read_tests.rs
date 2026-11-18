use super::*;

fn function_read(memory: &SharedMemory, address: &Address) -> Address {
    Address::symbolic_function(crate::kernel::eval::load_variable_for_exact_cell(
        memory,
        address,
        LoadKind::Int32,
        8,
    ))
}

fn callback_value(name: &str) -> ProgramValue {
    ProgramValue::typed_pointer(
        Address::function(name),
        ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED),
    )
}

#[test]
fn function_pointer_read_requires_explicit_store_equation() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = Address {
        base: "callback-slot".into(),
        offset: AddressOffset::Constant(0),
    };
    let target = Address::function("callback");
    let stored = callback_value("callback");
    let memory = intern_memory(SymbolicMemory::new().store(slot.clone(), stored.clone()));
    for aliased in [false, true] {
        let query = if aliased {
            Address::symbolic(Variable(992001))
        } else {
            slot.clone()
        };
        let read = function_read(&memory, &query);
        let empty = PureFactContext::new().assume_condition(
            ConditionTerm::address_equal(slot.clone(), query.clone()),
            true,
        );
        assert!(
            !empty.pointers_known_equal(&read, &target),
            "cached value leaked, alias={aliased}"
        );
        let equation =
            crate::kernel::memory_history::store_value_equation(memory.memory(), &slot, &stored)
                .expect("function store equation");
        let facts = empty.clone().assume_proposition(equation.clone());
        assert!(facts.pointers_known_equal(&read, &target));
        assert!(!empty.pointers_known_equal(&read, &target));
        if aliased {
            let before_alias = PureFactContext::new().assume_proposition(equation);
            assert!(!before_alias.pointers_known_equal(&read, &target));
            let after_alias = before_alias.assume_condition(
                ConditionTerm::address_equal(slot.clone(), query.clone()),
                true,
            );
            assert!(after_alias.pointers_known_equal(&read, &target));
        }
        let replacement = callback_value("replacement");
        let after = intern_memory(
            memory
                .memory()
                .clone()
                .store(slot.clone(), replacement.clone()),
        );
        let new_read = function_read(&after, &query);
        assert!(!facts.pointers_known_equal(&new_read, &Address::function("replacement")));
        let updated = facts.assume_proposition(
            crate::kernel::memory_history::store_value_equation(
                after.memory(),
                &slot,
                &replacement,
            )
            .unwrap(),
        );
        assert!(updated.pointers_known_equal(&new_read, &Address::function("replacement")));
        assert!(!updated.pointers_known_equal(&new_read, &target));
        assert!(updated.pointers_known_equal(&read, &target));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/function_read_tests.rs");
}
