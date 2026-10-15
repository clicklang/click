// Scaling tests of `src/surface/proof/claim_proofs.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

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
