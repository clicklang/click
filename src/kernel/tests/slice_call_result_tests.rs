//! Slices named by one variable (`design/rust-slice-values.md`, step
//! 2b-iii-a): a slice-returning call's result, and every other value
//! `symbolic_call_result` names by one variable, is a wide pointer whose thin
//! part is the variable's address and whose count is the variable's element
//! count, [`Variable::element_count`].
use super::*;
use crate::kernel::VerificationSession;

fn bytes() -> ProgramType {
    ProgramType::SlicePointer(SliceElement::UInt8)
}

/// The slice `symbolic_call_result` names by `variable`, as a pointer.
fn named_slice(program_type: ProgramType, variable: Variable) -> Pointer {
    let ProgramValue::Pointer(pointer) = symbolic_call_result(program_type, variable) else {
        panic!("a slice is a pointer value");
    };
    pointer
}

/// A count is its own variable: not its slice's variable, not an ordinary,
/// bound or produced variable, and ordered after every variable that is not
/// a count, so the greatest ordinary variable is still bounded by
/// `FIRST_NON_ORDINARY`. Its slice is read back from it.
#[test]
fn a_variable_names_its_element_count() {
    let ordinary = Variable(964_000);
    let produced = Variable::produced(Producer::TerminationParameter, 3);
    for variable in [ordinary, produced] {
        let count = variable.element_count();
        assert_ne!(count, variable);
        assert_eq!(count.counted_slice(), Some(variable));
        assert_eq!(variable.counted_slice(), None);
        assert!(!count.is_ordinary() && !count.is_bound());
        assert_eq!(count.producer(), None);
        assert!(count > Variable::FIRST_NON_ORDINARY);
        assert_eq!(
            std::collections::HashSet::from([variable, count]).len(),
            2,
            "a count hashes apart from its slice's variable"
        );
    }
    assert_ne!(ordinary.element_count(), produced.element_count());
    assert!(ordinary.is_ordinary());
    assert_eq!(produced.producer(), Some(Producer::TerminationParameter));
}

#[test]
#[should_panic(expected = "an element count names no slice")]
fn a_count_has_no_count() {
    let _ = Variable(964_001).element_count().element_count();
}

/// A slice-typed value named by one variable is a wide pointer: its thin
/// part is the variable's address at the element's pointer type, and its
/// count is the variable's count. A `str` keeps its type.
#[test]
fn a_slice_named_by_a_variable_names_its_count() {
    let _session = VerificationSession::enter();
    let variable = Variable(964_010);
    let slice = named_slice(bytes(), variable);
    assert!(slice.is_wide());
    assert_eq!(slice.program_type(), bytes());
    let thin = slice.as_ptr();
    assert_eq!(thin.address(), &Address::symbolic(variable));
    assert_eq!(thin.program_type(), ProgramType::UInt8Pointer);
    assert_eq!(
        slice.len(),
        Some(&OldMachineTerm::Variable(variable.element_count()))
    );

    let text = ProgramType::SlicePointer(SliceElement::Str);
    let string = named_slice(text, Variable(964_011));
    assert_eq!(string.program_type(), text);
    assert_eq!(
        string.len(),
        Some(&OldMachineTerm::Variable(Variable(964_011).element_count()))
    );

    // One name gives one slice; two names give two counts.
    assert_eq!(named_slice(bytes(), variable), slice);
    assert_ne!(named_slice(bytes(), Variable(964_012)).len(), slice.len());
}

/// A call of a contract-only function returning a slice binds a wide
/// result whose count is named by that call's result, so two calls return
/// two slices with two counts, and neither count is a fact-derived value.
#[test]
fn slice_returning_calls_name_their_counts() {
    let _session = VerificationSession::enter();
    let helper = program_function(
        bytes(),
        "opaque_slice",
        Vec::new(),
        program_return(ProgramExpression::Value(ProgramValue::Pointer(
            Pointer::new(
                Address::symbolic(Variable(964_020)),
                ProgramType::UInt8Pointer,
            )
            .with_element_count(OldMachineTerm::Variable(Variable(964_021))),
        ))),
    )
    .with_contract(Vec::new(), Vec::new(), Vec::new(), Vec::new(), true);
    let environment = ExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(VerifiedFunctionRule {
            pointer_result: None,
            function: helper,
            descent_completion: None,
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::Verify,
            checked_callees: None,
            applied_tactics: Default::default(),
        });
    let initial = |id: u64| {
        ProgramValue::Pointer(
            Pointer::new(Address::symbolic(Variable(id)), ProgramType::UInt8Pointer)
                .with_element_count(OldMachineTerm::Variable(Variable(id + 1))),
        )
    };
    let statement = program_seq(
        program_call_then_assign(4, "first", "opaque_slice", Vec::new()),
        program_seq(
            program_call_then_assign(5, "second", "opaque_slice", Vec::new()),
            program_return(crate::kernel::program_expression::variable("second")),
        ),
    );
    let execution = prove_symbolic_program_execution_paths_with_environment(
        ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("first", initial(964_030))
            .with_local("second", initial(964_032)),
        statement,
        PureFactContext::new(),
        environment,
        ExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("calls should execute");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::ProgramStatementVerifies {
        outcome: StatementOutcome::Return { value, state },
        ..
    } = proposition
    else {
        panic!("calls should return normally")
    };
    let slice = |name: &str| {
        let local = state.locals().get_native(name);
        let Some(ProgramValue::Pointer(pointer)) = local.as_deref() else {
            panic!("{name} holds a slice: {local:?}");
        };
        pointer.clone()
    };
    let (first, second) = (slice("first"), slice("second"));
    for result in [&first, &second] {
        assert!(result.is_wide(), "{result:?}");
        let AddressBase::Symbolic(variable) = result.as_ptr().address().base else {
            panic!("a call result is named by its variable: {result:?}");
        };
        assert_eq!(
            result.len(),
            Some(&OldMachineTerm::Variable(variable.element_count()))
        );
    }
    assert_ne!(first.len(), second.len());
    assert_eq!(
        value.native().as_ref(),
        &ProgramValue::Pointer(second.clone())
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/slice_call_result_tests.rs");
}
