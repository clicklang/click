// Scaling tests of `src/surface/proof/execution_state.rs` (module `loop_return_routing_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn loop_return_closer_routing_scales_with_certificate_size() {
    for size in [16, 64, 256] {
        let mut steps = Vec::new();
        let mut returns = Vec::new();
        for index in 0..size {
            steps.push(ProofStep::Loop(CertificateStructuralClause {
                region: CodeRegion::Loop(index),
                label: None,
                decreases: None,
                diverges: false,
                items: Vec::new(),
                resources: Vec::new(),
                initialize_proof: None,
                preserve_proof: Some(Box::new(
                    ProofCertificate::from_steps(vec![ProofStep::Step]).unwrap(),
                )),
            }));
            returns.push((
                Arc::new(LoopReturnProof {
                    loop_index: index,
                    owners: PersistentSequence::default(),
                    case_path: Vec::new(),
                    tactics: PersistentSequence::default(),
                    capture: None,
                    batch_captures: imbl::OrdMap::new(),
                }),
                Vec::new(),
                vec![ProofTactic::Assumption],
                Vec::new(),
            ));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            append_loop_return_closers(&mut steps, &returns, None)
        });
        result.unwrap();
        assert!(work <= 8 * size, "{size} loops required {work} work units");
        for step in steps {
            let ProofStep::Loop(clause) = step else {
                unreachable!()
            };
            assert!(matches!(
                clause.preserve_proof.unwrap().steps(),
                [ProofStep::Step, ProofStep::Assumption]
            ));
        }
    }
}

#[test]
fn surface_suffix_append_borrows_steps_on_a_small_stack() {
    for depth in [4usize, 16, 64, 112, 256] {
        for selected in [false, true] {
            std::thread::Builder::new()
                .name(format!("surface-suffix-{depth}-{selected}"))
                .stack_size(2 * 1024 * 1024)
                .spawn(move || {
                    // All fixture steps are already simple. Build their
                    // shared lists directly so this test isolates appending.
                    let certificate = |steps| ProofCertificate {
                        steps: Arc::new(steps),
                        pruned_execution_arm: false,
                    };
                    let mut existing = certificate(vec![ProofStep::Step]);
                    let mut suffix = certificate(vec![ProofStep::Normalize]);
                    for index in 0..depth {
                        let condition = ClickProposition::Comparison {
                            left: ContractExpression::CFragment(CExpression::Variable(format!(
                                "b{index}"
                            ))),
                            operator: ComparisonOperator::Equal,
                            right: ContractExpression::CFragment(CExpression::Value(
                                crate::kernel::int32(1),
                            )),
                        };
                        existing = certificate(vec![ProofStep::If {
                            condition: condition.clone(),
                            ensuring: None,
                            then_proof: Box::new(existing),
                            else_proof: Box::new(certificate(vec![ProofStep::Step])),
                        }]);
                        if selected {
                            suffix = certificate(vec![ProofStep::If {
                                condition,
                                ensuring: None,
                                then_proof: Box::new(suffix),
                                else_proof: Box::new(certificate(vec![ProofStep::Normalize])),
                            }]);
                        }
                    }
                    let mut steps = existing.into_steps();
                    let step = suffix.into_steps().pop().unwrap();
                    SURFACE_LEAF_VISITS.with(|visits| visits.set(0));
                    append_surface_step_to_leaves(&mut steps, step);
                    let visits = SURFACE_LEAF_VISITS.with(|visits| visits.get());
                    assert_eq!(visits, 2 * depth + 1);
                    let mut pending = vec![steps.as_slice()];
                    let mut leaves = 0;
                    while let Some(steps) = pending.pop() {
                        match steps {
                            [
                                ProofStep::If {
                                    then_proof,
                                    else_proof,
                                    ..
                                },
                            ] => {
                                pending.push(then_proof.steps());
                                pending.push(else_proof.steps());
                            }
                            [ProofStep::Step, ProofStep::Normalize] => leaves += 1,
                            _ => panic!("unexpected appended leaf"),
                        }
                    }
                    assert_eq!(leaves, depth + 1);
                })
                .unwrap()
                .join()
                .unwrap();
        }
    }
}
