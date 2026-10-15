use super::*;

fn guard(operator: CComparisonOperator, value: u32) -> SpecProposition {
    SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("active")),
        operator,
        right: SpecExpression::CExpression(c_int32_literal(value)),
    }
}

fn segment(guard: Option<SpecProposition>, start: u32, end: u32) -> CMemorySegment {
    let segment = CMemorySegment::new(
        c_variable("cells"),
        c_int32_literal(start),
        c_int32_literal(end),
    );
    match guard {
        Some(guard) => segment.with_guard(guard),
        None => segment,
    }
}

fn function_with_segment(name: &str, segment: CMemorySegment) -> CFunction {
    c_function(CType::Void, name, Vec::new(), c_return(c_void_value())).with_contract(
        Vec::new(),
        Vec::new(),
        vec![segment],
        Vec::new(),
        true,
    )
}

fn entry_state() -> CState {
    CState::new()
        .with_local(
            "active",
            int32(Bitvector32Term::Variable(Variable(980_001))),
        )
        .with_local(
            "cells",
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
}

fn compatible_with_assumptions(
    contract: &CFunction,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> bool {
    let entry = entry_state();
    mutable_footprint_is_compatible(
        contract,
        function,
        &entry,
        &entry,
        assumptions,
        &mut ExecutionBudget::new(),
    )
    .expect("guarded mutable refinement should execute")
}

fn compatible(contract: &CFunction, function: &CFunction) -> bool {
    compatible_with_assumptions(contract, function, &PureFactContext::new())
}

#[test]
fn stronger_concrete_guard_and_subrange_refine_named_footprint() {
    let contract = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
    );
    let function = function_with_segment(
        "function",
        segment(Some(guard(CComparisonOperator::Equal, 1)), 1, 2),
    );
    assert!(compatible(&contract, &function));
}

#[test]
fn guarded_concrete_effect_refines_unguarded_named_footprint() {
    let contract = function_with_segment("contract", segment(None, 0, 2));
    let function = function_with_segment(
        "function",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
    );
    assert!(compatible(&contract, &function));
}

#[test]
fn unguarded_concrete_effect_does_not_refine_guarded_named_footprint() {
    let contract = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
    );
    let function = function_with_segment("function", segment(None, 0, 1));
    assert!(!compatible(&contract, &function));
}

#[test]
fn unrelated_concrete_guard_does_not_refine_named_guard() {
    let contract = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::GreaterThan, 0)), 0, 2),
    );
    let function = function_with_segment(
        "function",
        segment(Some(guard(CComparisonOperator::LessThan, 0)), 0, 1),
    );
    assert!(!compatible(&contract, &function));
}

fn active_is_zero(value: bool) -> PureFactContext {
    PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(980_001)),
            Bitvector32Term::Constant(0),
        ),
        value,
    ))
}

/// An available guard that only logical search could discharge is treated
/// as unsettled, so its segment is not available. The same footprint with
/// the guard spelled as the exactly available condition is accepted, so
/// the difference is the route rather than the content.
#[test]
fn disjunctive_available_guard_is_not_discharged_by_search() {
    let exact = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
    );
    let disjunctive = function_with_segment(
        "contract",
        segment(
            Some(SpecProposition::Or(
                Box::new(guard(CComparisonOperator::NotEqual, 0)),
                Box::new(guard(CComparisonOperator::Equal, 5)),
            )),
            0,
            2,
        ),
    );
    let function = function_with_segment("function", segment(None, 0, 1));
    let assumptions = active_is_zero(false);
    assert!(compatible_with_assumptions(&exact, &function, &assumptions));
    assert!(!compatible_with_assumptions(
        &disjunctive,
        &function,
        &assumptions
    ));
}

/// A required segment whose guard is exactly refuted contributes no write,
/// so nothing has to cover it. Without that refutation the same footprint
/// is wider than the contract's and is rejected.
#[test]
fn exactly_refuted_required_guard_needs_no_cover() {
    let contract = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 1),
    );
    let function = function_with_segment(
        "function",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
    );
    assert!(compatible_with_assumptions(
        &contract,
        &function,
        &active_is_zero(true)
    ));
    assert!(!compatible(&contract, &function));
}

#[test]
fn guard_implication_does_not_relax_range_containment() {
    let contract = function_with_segment(
        "contract",
        segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
    );
    let function = function_with_segment(
        "function",
        segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 2),
    );
    assert!(!compatible(&contract, &function));
}
