use super::*;
use crate::kernel::{
    CFunctionContractClaim, CStatement, Proposition, bool_value, c_call, c_function, c_if,
    c_int32_literal, c_parameter, c_return, c_seq, c_skip, c_try_catch_int32, c_variable,
    prove_c_function_contract_execution_paths_with_checked_artifacts,
    prove_checked_c_function_execution_with_environment,
};

/// A caught-throw call splits into its returned and threw arms the way a C
/// `if` splits: the call runs in the proof's context, and each arm is the
/// proof's facts with what the call added. Splitting after `size`
/// unrelated facts copies none of them and costs no more at any size (the
/// first size also pays one-time warm-up); it once copied every fact into a
/// flat list and folded each one back, and its work grew from 600 to 7,296
/// units at 16 to 256 facts.
#[test]
fn call_outcome_split_does_not_copy_the_proofs_facts() {
    let helper = c_function(
        CType::Int32,
        "helper",
        vec![c_parameter("should_throw", CType::Bool)],
        c_if(
            c_variable("should_throw"),
            CStatement::Throw(c_int32_literal(7)),
            c_return(c_int32_literal(5)),
        ),
    )
    .with_int32_exceptional_outcome()
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let helper_arguments = vec![CExpression::Value(bool_value(Bitvector32Term::Variable(
        Variable(80_111),
    )))];
    let artifacts = prove_checked_c_function_execution_with_environment(
        CState::new().with_population_creation_tracking(),
        helper.clone(),
        helper_arguments.clone(),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let certified = prove_c_function_contract_execution_paths_with_checked_artifacts(
        CState::new().with_population_creation_tracking(),
        helper.clone(),
        helper_arguments,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
        &[artifacts],
    );
    let claims = crate::kernel::c_verified_function_contract_claims(&helper, &certified)
        .expect("helper body safety should certify");
    let helper_rule = c_verified_function_rule(helper.clone(), &claims)
        .expect("the checked helper should have a modular rule");
    let function_environment = CExecutionEnvironment::new()
        .with_function(helper)
        .with_verified_function_rule(helper_rule);
    let function = c_function(
        CType::Int32,
        "caller",
        vec![
            c_parameter("construct", CType::Bool),
            c_parameter("should_throw", CType::Bool),
        ],
        c_seq(
            c_if(
                c_variable("construct"),
                c_try_catch_int32(
                    c_call("helper", vec![c_variable("should_throw")]),
                    "caught",
                    c_return(c_variable("caught")),
                ),
                c_skip(),
            ),
            c_return(c_int32_literal(5)),
        ),
    );
    let parsed_function = syntax::C0Function::external(
        C0Type::Int32,
        "caller".into(),
        vec![
            syntax::C0Parameter::new(C0Type::Bool, "construct".into(), None),
            syntax::C0Parameter::new(C0Type::Bool, "should_throw".into(), None),
        ],
    )
    .with_prelowered_kernel_function(function.clone());
    let click_file = crate::surface::parse(
        "int32 caller(bool construct, bool should_throw) { ensures result == result; }",
    )
    .unwrap();
    let function_block = &click_file.function_blocks()[0];
    let arguments = vec![
        CExpression::Value(bool_value(Bitvector32Term::Variable(Variable(80_112)))),
        CExpression::Value(bool_value(Bitvector32Term::Variable(Variable(80_113)))),
    ];
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let theorems = TheoremEnvironment::new(&[]);
    let resources = ResourceEnvironment::new(&[]);
    let constants = ExecutionProofConstants {
        source_layout: SourceExecutionLayout::for_function(&parsed_function).unwrap(),
        ..ExecutionProofConstants::default()
    };
    let mut costs = Vec::new();
    for size in [16u64, 64, 256] {
        let facts = (0..size)
            .map(|index| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(Bitvector32Term::Variable(Variable(81_000 + index))),
                        right: Box::new(Bitvector32Term::Constant(index as u32)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        let root = Proof::for_execution_frontier(
            "call outcome split",
            0,
            ExecutionProofState::at_entry(
                CState::new().with_population_creation_tracking(),
                ExecutionFrontier::default(),
                RecordedSnapshots::new(),
                SurfacePropositionMap::default(),
                PersistentSequence::default(),
            ),
            facts.clone(),
            constants.clone(),
            function_block,
            &function,
            &parsed_function,
            &arguments,
            &function_environment,
            &resources,
            SpecDefinitions::new(&predicates, &functions),
            &theorems,
        );
        let (branch, branch_record) = root
            .split_focused_execution_branch()
            .expect("the conditional should split");
        let at_call = branch.focus_split_arm(&branch_record, true).unwrap();
        let [copied_before, _] = crate::surface::pure_fact_list::fact_list_entry_counts();
        let (split, work) = crate::instrumentation::measure_deterministic_work(|| {
            at_call
                .split_focused_call_outcomes()
                .expect("the call split should be checked")
                .expect("the helper both returns and throws")
        });
        let [copied_after, _] = crate::surface::pure_fact_list::fact_list_entry_counts();
        let (outcomes, record) = split;
        let returned = outcomes.focus_split_arm(&record, true).unwrap();
        let threw = outcomes.focus_split_arm(&record, false).unwrap();
        for arm in [&returned, &threw] {
            assert!(
                facts.iter().all(|fact| arm.facts().contains(fact)),
                "an arm lost a fact of the proof: size={size}"
            );
        }
        costs.push((copied_after - copied_before, work));
    }
    assert!(
        costs
            .windows(2)
            .all(|pair| pair[1].0 <= pair[0].0 && pair[1].1 <= pair[0].1),
        "splitting a call's outcomes grows with the proof's facts: {costs:?}"
    );
}
