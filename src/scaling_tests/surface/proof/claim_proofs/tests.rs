// Scaling tests of `src/surface/proof/claim_proofs.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn explicit_closers_lower_each_return_goal_once_without_unfoldings() {
    use crate::instrumentation::{VerificationEvent, collect, measure_deterministic_work};
    crate::surface::verify_c0_sources("theorem warm() { ensures true by normalize(); }", &[])
        .unwrap();
    for size in [2, 4, 8, 16] {
        let claims = "ensures result == x;\n".repeat(size);
        let closers = "assumption();\n".repeat(size);
        let source = format!(
            "verifying \"echo.c\"; int32 echo(int32 x) {{ {claims} }} by {{ step(); {closers} }}"
        );
        let ((verified, events), work) = measure_deterministic_work(|| {
            collect(|| {
                crate::surface::verify_c0_sources(
                    &source,
                    &[("echo.c", "int32 echo(int32 x) { return x; }")],
                )
            })
        });
        assert_eq!(verified.unwrap().len(), size);
        let lowerings = events
            .iter()
            .filter(|event| {
                matches!(event,
                    VerificationEvent::OperationFinished { function, name, .. }
                        if function == "echo" && name == "return claim goal lowering"
                )
            })
            .count();
        eprintln!("return-goal lowerings: claims={size}, lowerings={lowerings}, work={work}");
        assert_eq!(lowerings, size, "each exact closer needs one goal lowering");
    }
}

#[test]
fn joint_resource_receipts_ignore_unrelated_holdings() {
    use crate::kernel::{Bitvector32Term, CResource, CResourceFact, ResourceContext};
    fn unit(name: String) -> CResourceFact {
        CResourceFact::Own(
            CResource::Token {
                name,
                arguments: vec![].into(),
            },
            Box::new(Bitvector32Term::Constant(1)),
        )
    }
    for size in [64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let selected = unit("returned".into());
        let available = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| unit(format!("unrelated_{index}"))))
            .unchecked_with_fact(selected.clone());
        let receipts = ResourceContext::new().unchecked_with_fact(selected.clone());
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resource_receipts_jointly_available(&available, &receipts, &assumptions)
        });
        assert!(accepted);
        assert!(work <= 16, "size={size}, work={work}");
        let duplicate = receipts.unchecked_with_fact(selected);
        assert!(!resource_receipts_jointly_available(
            &available,
            &duplicate,
            &assumptions
        ));
    }
}
