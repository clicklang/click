// Scaling tests of `src/kernel/functions.rs` (module `provisional_ensure_obligation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn provisional_ensure_loadability_work_ignores_unrelated_facts() {
    let memory = CMemory::new();
    let data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("data", CValue::pointer(data.clone()))
        .with_memory(memory.clone());
    let ensure = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::PointerOffset {
                object_bytes: None,
                pointer: Box::new(SpecExpression::CExpression(c_variable("data"))),
                elements: Box::new(SpecExpression::CExpression(c_int32_literal(1))),
                byte_width: 4,
            }),
            value_type: CType::Int32,
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let function = c_function(
        CType::Int32,
        "provisional_loadability_probe",
        vec![c_parameter("data", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(Vec::new(), vec![ensure], Vec::new(), Vec::new(), true);
    let base_assumptions =
        PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: data.clone(),
            bytes: Bitvector32Term::Constant(8),
            wide: false,
        });
    let element_loadable = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
        wide: false,
    };
    let mut work_by_size = Vec::new();
    for unrelated_count in [16, 64, 256, 1024] {
        let mut assumptions = base_assumptions.clone();
        for index in 0..unrelated_count {
            assumptions = assumptions.assume_proposition(Proposition::Predicate {
                name: format!("unrelated_{index}"),
                arguments: Vec::new(),
            });
        }
        let mut facts = crate::kernel::ExecutionFacts::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            add_verified_function_ensure_facts(
                &mut facts,
                &[],
                &state,
                &state,
                &function,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
        });
        result.expect("the provisional ensure should lower");
        assert!(
            !facts
                .iter()
                .any(|fact| fact.proposition() == &element_loadable),
            "a value postcondition must not publish viewability"
        );
        work_by_size.push((unrelated_count, work));
    }

    let baseline = work_by_size[0].1.max(1);
    let largest = work_by_size.last().unwrap().1;
    assert!(
        largest <= baseline * 2,
        "provisional ensure work should be independent of unrelated facts: {work_by_size:?}"
    );
}
