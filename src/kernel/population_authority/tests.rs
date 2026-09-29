use super::*;

#[test]
fn distributed_members_require_authority_and_must_return_before_retirement() {
    let owner = Holder::fresh();
    let worker = Holder::fresh();
    let (state, anchor) = AuthorityState::default().allocate_anchor(owner);
    let (state, population) = state.establish(owner, anchor, "reference").unwrap();
    let state = state.produce(owner, population, 2).unwrap();
    let state = state
        .transfer_members(owner, worker, population, 1)
        .unwrap();
    assert_eq!(state.observe(owner, population), Ok(2));
    assert_eq!(
        state.observe(worker, population),
        Err(Refusal::MissingAuthority)
    );
    assert_eq!(
        state.consume(worker, population, 1).unwrap_err(),
        Refusal::MissingAuthority
    );
    assert_eq!(
        state.finish_holder(worker),
        Err(Refusal::OutstandingOwnership)
    );
    let state = state.transfer_authority(owner, worker, population).unwrap();
    let state = state.consume(worker, population, 1).unwrap();
    assert_eq!(
        state.consume(worker, population, 1).unwrap_err(),
        Refusal::MissingMembers
    );
    assert_eq!(
        state.retire(worker, population).unwrap_err(),
        Refusal::OutstandingMembers
    );
    let state = state
        .transfer_members(owner, worker, population, 1)
        .unwrap();
    let state = state.consume(worker, population, 1).unwrap();
    let state = state.retire(worker, population).unwrap();
    assert_eq!(state.finish_holder(worker), Ok(()));
    let state = state.free_anchor(owner, anchor).unwrap();
    assert_eq!(state.finish_holder(owner), Ok(()));
}

#[test]
fn registration_survives_anchor_and_authority_transfers() {
    let owner = Holder::fresh();
    let receiver = Holder::fresh();
    let (state, anchor) = AuthorityState::default().allocate_anchor(owner);
    let (state, population) = state.establish(owner, anchor, "reference").unwrap();
    let state = state.transfer_anchor(owner, receiver, anchor).unwrap();
    assert_eq!(
        state.establish(receiver, anchor, "reference").unwrap_err(),
        Refusal::AlreadyRegistered
    );
    assert_eq!(
        state.free_anchor(receiver, anchor).unwrap_err(),
        Refusal::OutstandingAuthority
    );
    assert_eq!(
        state.establish(owner, anchor, "other").unwrap_err(),
        Refusal::MissingAnchor
    );
    let state = state
        .transfer_authority(owner, receiver, population)
        .unwrap();
    assert_eq!(state.finish_holder(owner), Ok(()));
    assert_eq!(
        state.finish_holder(receiver),
        Err(Refusal::OutstandingOwnership)
    );
    let state = state.retire(receiver, population).unwrap();
    let (state, replacement) = state.establish(receiver, anchor, "reference").unwrap();
    assert_ne!(population, replacement);
    assert_eq!(
        state.observe(receiver, population),
        Err(Refusal::UnknownPopulation)
    );
    assert_eq!(state.observe(receiver, replacement), Ok(0));
}

#[test]
fn all_registered_families_must_retire_before_anchor_free() {
    let owner = Holder::fresh();
    let (state, anchor) = AuthorityState::default().allocate_anchor(owner);
    let (state, first) = state.establish(owner, anchor, "reference").unwrap();
    let (state, second) = state.establish(owner, anchor, "slot").unwrap();
    let state = state.retire(owner, first).unwrap();
    assert_eq!(
        state.free_anchor(owner, anchor).unwrap_err(),
        Refusal::OutstandingAuthority
    );
    let state = state.retire(owner, second).unwrap();
    let state = state.free_anchor(owner, anchor).unwrap();
    assert_eq!(
        state.establish(owner, anchor, "reference").unwrap_err(),
        Refusal::MissingAnchor
    );
}

#[test]
fn invalid_quantities_and_double_spending_preserve_the_input() {
    let owner = Holder::fresh();
    let worker = Holder::fresh();
    let (state, anchor) = AuthorityState::default().allocate_anchor(owner);
    let (state, population) = state.establish(owner, anchor, "reference").unwrap();
    assert_eq!(
        state.produce(owner, population, 0).unwrap_err(),
        Refusal::InvalidQuantity
    );
    let state = state.produce(owner, population, i32::MAX as u32).unwrap();
    assert_eq!(
        state.produce(owner, population, 1).unwrap_err(),
        Refusal::InvalidQuantity
    );
    let state = state
        .transfer_members(owner, worker, population, i32::MAX as u32)
        .unwrap();
    assert_eq!(
        state
            .transfer_members(owner, worker, population, 1)
            .unwrap_err(),
        Refusal::MissingMembers
    );
    assert_eq!(state.observe(owner, population), Ok(i32::MAX as u32));
}

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
fn mixed_transitions_conserve_totals_and_cleanup_obligations() {
    let holders = [Holder::fresh(), Holder::fresh(), Holder::fresh()];
    let (state, anchor) = AuthorityState::default().allocate_anchor(holders[0]);
    let (mut state, population) = state.establish(holders[0], anchor, "reference").unwrap();
    let mut seed = 17_u64;
    for _ in 0..1000 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        let from = holders[(seed as usize >> 8) % holders.len()];
        let to = holders[(seed as usize >> 16) % holders.len()];
        let result = match seed % 5 {
            0 => state.produce(from, population, 1),
            1 => state.consume(from, population, 1),
            2 => state.transfer_members(from, to, population, 1),
            3 => state.transfer_authority(from, to, population),
            _ => state.transfer_anchor(from, to, anchor),
        };
        if let Ok(next) = result {
            state = next;
        }
        // Independent test oracle: production operations must use indexed
        // deltas, but tests may enumerate ownership to check conservation.
        let sum: u32 = state.members.iter().map(|(_, quantity)| *quantity).sum();
        assert_eq!(sum, state.populations.get(&population).unwrap().total);
        for holder in holders {
            let members: u64 = state
                .members
                .iter()
                .filter(|((owner, _), _)| *owner == holder)
                .map(|(_, quantity)| u64::from(*quantity))
                .sum();
            let anchors = state
                .anchors
                .iter()
                .filter(|(_, r)| r.owner == holder)
                .count() as u64;
            let authorities = state
                .populations
                .iter()
                .filter(|(_, r)| r.owner == holder)
                .count() as u64;
            assert_eq!(
                state.obligations.get(&holder).copied().unwrap_or(0),
                members + anchors + authorities
            );
        }
    }
}
