// Candidate-count scaling for target-guided quantified equality queries.
use super::*;

#[test]
fn guided_condition_instantiation_skips_unrelated_target_variables_scaling() {
    let _session = crate::kernel::VerificationSession::enter();
    for count in [16, 128, 1024] {
        let target_term = (0..count).fold(0u32.into(), |sum, i| {
            Bitvector32Term::add(sum, variable(998_200 + i))
        });
        let target = ConditionTerm::equal(target_term, variable(999_500));
        // These scalars do not match any bound occurrence in the array
        // fact. None may trigger a speculative memory equality query.
        assert!(
            PureFactContext::guided_forall_condition_candidates(
                Variable(998_100),
                &body(),
                &target
            )
            .is_empty()
        );
    }
}
