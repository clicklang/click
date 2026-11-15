// Scaling tests of `src/kernel/termination.rs` (module `local_descent_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Each sequential `if` used to double the list of path bounds the
/// recursion checker carried, so a recursive function with a few dozen
/// of them before its ranked call could not be checked at all. The list
/// now holds one bound per join, which decides every edge the same way.
#[test]
fn a_recursion_check_is_linear_in_sequential_branches() {
    let n = || crate::kernel::program_expression::variable("n");
    let literal = |value: u32| crate::kernel::program_expression::int32_literal(value);
    let guarded_call = |argument: ProgramExpression| {
        crate::kernel::program_if(
            crate::kernel::program_expression::greater_than(n(), literal(0)),
            crate::kernel::program_call("countdown", vec![argument]),
            ProgramStatement::Skip,
        )
    };
    // A balanced sequence, so the walk's depth is logarithmic and the
    // test measures the branch count and not the nesting.
    fn sequence(statements: &[ProgramStatement]) -> ProgramStatement {
        match statements {
            [] => ProgramStatement::Skip,
            [only] => only.clone(),
            _ => {
                let (left, right) = statements.split_at(statements.len() / 2);
                ProgramStatement::seq(Arc::new(sequence(left)), Arc::new(sequence(right)))
            }
        }
    }
    let build = |branches: usize, descends: bool| {
        // Branches on the measure that establish nothing about it.
        let branches = (0..branches)
            .map(|index| {
                crate::kernel::program_if(
                    crate::kernel::program_expression::less_than(
                        n(),
                        literal(index as u32 + 1_000),
                    ),
                    ProgramStatement::Skip,
                    ProgramStatement::Skip,
                )
            })
            .collect::<Vec<_>>();
        let mut body = sequence(&branches);
        let argument = if descends {
            crate::kernel::program_expression::subtract(n(), literal(1))
        } else {
            n()
        };
        body = ProgramStatement::seq(Arc::new(body), Arc::new(guarded_call(argument)));
        [VerifiedFunctionRule {
            pointer_result: None,
            descent_completion: None,
            concrete_loop_exits: None,
            loop_semantics: LoopSemantics::ApplyVerifiedRules,
            checked_callees: None,
            applied_tactics: Default::default(),
            function: ProgramFunction::new(
                ProgramType::Void,
                "countdown",
                vec![crate::kernel::program_parameter("n", ProgramType::Int32)],
                body,
            ),
        }]
    };
    let plan = FunctionTerminationPlan {
        function_name: "countdown".to_string(),
        recursive_measure: Some(FunctionTerminationMeasure::NumericParameter(0)),
        loop_measures: BTreeMap::new(),
    };
    // Judged by the checker's deterministic work, not the host clock:
    // each 8x step in branches may cost at most 16x the work, which a
    // linear checker meets and a doubling path list cannot.
    let mut previous: Option<(usize, usize)> = None;
    for branches in [8, 64, 512] {
        let rules = build(branches, true);
        let heights = program_termination_height_plan(&rules, &[]);
        let (verdicts, work) = crate::instrumentation::measure_deterministic_work(|| {
            check(&rules, std::slice::from_ref(&plan), &heights, &[])
                .expect("a descending call checks")
        });
        assert_eq!(terminating(&verdicts), BTreeSet::from(["countdown"]));
        assert!(work >= branches, "the check charges each branch it walks");
        if let Some((smaller, smaller_work)) = previous {
            assert!(
                work <= smaller_work * 16,
                "{branches} sequential branches took {work} work units, \
                 over 16x the {smaller_work} units of {smaller}"
            );
        }
        previous = Some((branches, work));
    }
    let rules = build(64, false);
    let heights = program_termination_height_plan(&rules, &[]);
    let error = check(&rules, std::slice::from_ref(&plan), &heights, &[])
        .expect_err("a call that passes the measure unchanged does not descend");
    assert!(error.message.contains("must pass"), "{error}");
}

#[test]
fn independent_loop_measure_ownership_costs_its_explicit_strategy_outputs() {
    let function = self_call_in_loop_rule("drain").function;
    let template = loop_rule_for(&function, None);
    for count in [16, 64, 256, 512] {
        let rules = (0..count)
            .map(|index| {
                let mut rule = template.clone();
                let ProgramStatement::While {
                    ranking_measures, ..
                } = &mut rule.loop_statement
                else {
                    unreachable!();
                };
                *ranking_measures = vec![RankingComponent::Pure {
                    source: format!("level{index}(n)"),
                    expression: SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        "n".into(),
                    )),
                }];
                rule.loop_evidence = function
                    .open_loop_proof(0, rule.loop_statement.clone())
                    .unwrap()
                    .loop_evidence;
                rule
            })
            .collect::<Vec<_>>();
        let ((ranked, unranked), work) = crate::instrumentation::measure_deterministic_work(|| {
            verified_loop_ranking_measures(&rules)
        });
        assert_eq!(ranked[&0].len(), count);
        assert!(unranked.is_empty());
        assert!(work <= 16 * count + 32, "{count} strategies: {work} work");
        let last = ranked[&0].last().unwrap().clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            check_loops(
                &function.source_body,
                &BTreeMap::from([(0, last)]),
                &ranked,
                "drain",
                &mut 0,
                &mut Vec::new(),
            )
            .unwrap();
        });
        assert!(work <= count + 16, "{count} explicit measures: {work} work");
    }
}
