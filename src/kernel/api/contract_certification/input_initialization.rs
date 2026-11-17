//! Initialization promised by one admitted typed input clause. This constructs
//! a quantified entry fact; it neither enumerates cells nor consults history.
use super::*;

pub(super) fn initialized_input_range_fact(
    state: &ExecutionState,
    interface: &FunctionContractInterface,
    segment: &MemorySegment,
    range: &MemoryRange,
) -> Result<Option<Proposition>, String> {
    crate::instrumentation::record_deterministic_work(1);
    if segment.is_uninitialized() {
        return Ok(None);
    }
    let constructed = interface
        .construction_parameter()
        .and_then(|(index, _)| interface.parameters().get(index))
        .map(ProgramParameter::binding_name)
        .or_else(|| {
            (interface.aggregate_return_mode() == AggregateReturnMode::Construction)
                .then_some(&crate::kernel::CONTRACT_RESULT)
        });
    if let Some(constructed) = constructed {
        let mut names = BTreeSet::new();
        crate::kernel::loops::collect_variable_names(&segment.base, &mut names);
        if names.contains(constructed) {
            return Ok(None);
        }
    }
    let Some(value_type) =
        crate::kernel::eval::program_expression_pointee_type(state, &segment.base)
    else {
        return Ok(None);
    };
    // Aggregate descriptors may include padding or several differently typed
    // fields. They do not denote an array of one complete scalar cell type.
    let scalar = value_type.is_pointer()
        || matches!(
            value_type,
            ProgramType::Bool
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::Int32
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
                | ProgramType::Int128
                | ProgramType::UInt128
                | ProgramType::Float32
                | ProgramType::Float64
        );
    if !scalar
        || value_type.byte_width() != range.element_width()
        || segment
            .value_runs()
            .is_some_and(|runs| runs != [(0, value_type.byte_width())])
    {
        return Ok(None);
    }
    let var = Variable::allocate_fresh().ok_or("initialization binder identity exhausted")?;
    let index = MachineTerm::Variable(var);
    let (format, sort, lo, hi) = match range.wide_bounds() {
        Some((lo, hi)) => (
            MachineIntegerType::UInt64,
            Sort::ProgramInteger(MachineIntegerType::UInt64),
            lo,
            hi,
        ),
        None => (
            MachineIntegerType::Int32,
            Sort::ProgramInt32,
            range.start(),
            range.end(),
        ),
    };
    let condition = |relation, left, right| {
        Proposition::ConditionIs(
            ConditionTerm::machine_compare(format, relation, left, right),
            true,
        )
    };
    let guard = Proposition::And(
        Box::new(condition(
            CompareRelation::LessEqual,
            lo.clone(),
            index.clone(),
        )),
        Box::new(condition(
            CompareRelation::LessThan,
            index.clone(),
            hi.clone(),
        )),
    );
    let wide = format == MachineIntegerType::UInt64;
    let defined = Proposition::MemoryReadDefined {
        at: state.observation_point_id(),
        memory: state.memory().clone(),
        pointer: range
            .base()
            .offset_by_typed_elements(index, range.element_width(), wide, wide),
        value_type,
    };
    Ok(Some(Proposition::ForAll {
        name: BinderName::written("k"),
        var,
        sort,
        body: Box::new(Proposition::Implies(Box::new(guard), Box::new(defined))),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (ExecutionState, ProgramFunction, MemorySegment, MemoryRange) {
        let base = Pointer {
            block: PointerBlock::Concrete("initialized-input".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = ExecutionState::new().with_local(
            "p",
            ProgramValue::typed_pointer(base.clone(), ProgramType::Int32Pointer),
        );
        let segment = MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(8),
        );
        let function = program_function(
            ProgramType::Int32,
            "input",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let range = MemoryRange::new(base, 0u32.into(), 8u32.into());
        (state, function, segment, range)
    }

    #[test]
    fn only_admitted_initialized_clauses_publish_input_definedness() {
        for (active, uninitialized, expected) in
            [(true, false, 1), (false, false, 0), (true, true, 0)]
        {
            let (state, function, segment, range) = fixture();
            let resource = ResourceSpec::owned_memory(segment.with_uninitialized(uninitialized))
                .with_guard(SpecProposition::Comparison {
                    left: SpecExpression::Value(int32(0)),
                    operator: ComparisonOperator::Equal,
                    right: SpecExpression::Value(int32(if active { 0 } else { 1 })),
                });
            let function = function.with_resource_summary(vec![resource], vec![]);
            let arguments = vec![ProgramExpression::Value(
                state.locals.get_native("p").unwrap().as_ref().clone(),
            )];
            let caller = ExecutionState::new().with_resource_context(
                ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range)),
            );
            let (_, facts, _) =
                super::super::program_function_contract_entry_facts(&caller, &function, &arguments)
                    .unwrap();
            assert_eq!(
                facts
                    .iter()
                    .filter(|fact| fact.origin() == ContractEntryFactOrigin::ClauseInitialized)
                    .count(),
                expected,
                "active={active}, uninitialized={uninitialized}"
            );
        }
    }

    mod scaling_tests {
        include!(
            "../../../scaling_tests/kernel/api/contract_certification/input_initialization.rs"
        );
    }
}
