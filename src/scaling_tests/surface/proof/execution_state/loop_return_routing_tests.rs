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
