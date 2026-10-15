// Scaling tests of `src/kernel/population_authority/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn unrelated_populations_do_not_make_transfers_linear() {
    for size in [8_u32, 32, 128, 512] {
        let owner = Holder::fresh();
        let receiver = Holder::fresh();
        let mut state = AuthorityState::default();
        let mut target = None;
        for _ in 0..size {
            let (next, anchor) = state.allocate_anchor(owner);
            let (next, population) = next.establish(owner, anchor, "reference").unwrap();
            state = next.produce(owner, population, 2).unwrap();
            target = Some(population);
        }
        let (next, work) = crate::persistent::measure_persistent_work(|| {
            state
                .transfer_members(owner, receiver, target.unwrap(), 1)
                .unwrap()
        });
        assert!(
            work < 100 * (size.ilog2() as usize + 1),
            "size={size}, work={work}"
        );
        assert_eq!(next.observe(owner, target.unwrap()), Ok(2));
    }
}

#[test]
fn establishment_and_retirement_are_indexed_by_scope() {
    for size in [8_u32, 32, 128, 512] {
        let creator = Holder::fresh();
        let (mut state, anchor) = AuthorityState::default().allocate_anchor(creator);
        for n in 0..size {
            let (next, population) = state
                .establish(creator, anchor, &format!("family{n}"))
                .unwrap();
            state = next.retire(creator, population).unwrap();
        }
        let ((state, population), work) = crate::persistent::measure_persistent_work(|| {
            state.establish(creator, anchor, "target").unwrap()
        });
        assert!(
            work < 100 * (size.ilog2() as usize + 1),
            "establish size={size}, work={work}"
        );
        let (state, work) = crate::persistent::measure_persistent_work(|| {
            state.retire(creator, population).unwrap()
        });
        assert!(
            work < 100 * (size.ilog2() as usize + 1),
            "retire size={size}, work={work}"
        );
        assert_eq!(
            state.establish(creator, anchor, "family0").unwrap_err(),
            Refusal::AlreadyEstablished
        );
        assert!(state.free_anchor(creator, anchor).is_ok());
    }
}
