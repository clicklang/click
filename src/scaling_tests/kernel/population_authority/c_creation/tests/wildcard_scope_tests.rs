// Scaling tests of `src/kernel/population_authority/c_creation/tests.rs` (module `wildcard_scope_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wildcard_helper_transfer_does_not_scan_unrelated_imports() {
    let samples = [16_u32, 64, 256, 1024].map(|size| {
        let (scope, member) = opaque_scope(0);
        let mut entry = CreationEvents::new()
            .import_opaque_wildcard_population(&scope, &member)
            .unwrap();
        for index in 1..=size {
            let (other, member) = opaque_scope(index);
            entry = entry
                .import_opaque_wildcard_population(&other, &member)
                .unwrap();
        }
        let helper = entry.enter_call();
        let ((held, work), indexed_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let held = entry
                    .transfer_call_fact(&entry, &helper, &scope, true)
                    .unwrap();
                held.transfer_call_fact(&entry, &helper, &member, false)
                    .unwrap()
            })
        });
        let held = held.return_to(&helper);
        assert!(held.owns_imported_population_member(&member));
        assert!(held.observe_symbolic(&scope).is_some());
        assert!(work > 0);
        indexed_work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 64 * index, "{samples:?}");
    }
}

#[test]
fn wildcard_helper_death_does_not_scan_unrelated_imports() {
    let samples = [16_u32, 64, 256, 1024].map(|size| {
        let (scope, member) = opaque_scope(0);
        let mut entry = CreationEvents::new()
            .import_opaque_wildcard_population(&scope, &member)
            .unwrap();
        for index in 1..=size {
            entry = entry
                .import_opaque_wildcard_authority(&opaque_scope(index).0)
                .unwrap();
        }
        let (spent, work) = crate::persistent::measure_persistent_work(|| {
            entry
                .checked_member_exchange(&PointerBlock::ExternalArgument, &member, false)
                .unwrap()
                .0
        });
        assert_eq!(spent.observe_symbolic(&scope).unwrap().delta, -1);
        assert_eq!(spent.observe_symbolic(&opaque_scope(1).0).unwrap().delta, 0);
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 32 * index, "{samples:?}");
    }
}

#[test]
fn exclusive_member_update_and_transfer_scale_over_neighboring_members() {
    let samples = [16_u32, 64, 256, 1024].map(|size| {
        let (scope, first) = opaque_scope(0);
        let at = |index| {
            let mut arguments = first.arguments().to_vec();
            arguments[1] = int32(index).into();
            ResourceDescription::new(
                first.family().into(),
                arguments.into(),
                first.schema().clone(),
            )
        };
        let mut events = CreationEvents::new()
            .import_opaque_wildcard_authority(&scope)
            .unwrap();
        let bounds = PureFactContext::new().assume_condition(
            ConditionTerm::signed_greater_equal(
                Bitvector32Term::Constant(i32::MAX as u32 - size - 1),
                events.observe_symbolic(&scope).unwrap().entry_count,
            ),
            true,
        );
        for index in 0..size {
            events = events
                .checked_exclusive_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &at(index),
                    true,
                    &Bitvector32Term::Constant(1),
                    &bounds,
                )
                .unwrap()
                .0;
        }
        let selected = at(size / 2);
        let child = events.enter_call();
        let ((), work) = crate::persistent::measure_persistent_work(|| {
            let sent = child
                .transfer_call_fact(&events, &child, &scope, true)
                .unwrap()
                .transfer_call_fact(&events, &child, &selected, false)
                .unwrap();
            let spent = sent
                .checked_member_exchange(&PointerBlock::ExternalArgument, &selected, false)
                .unwrap()
                .0;
            let returned = spent
                .transfer_call_fact(&child, &events, &scope, true)
                .unwrap()
                .finish_call(&events)
                .unwrap();
            assert!(!returned.owns_imported_population_member(&selected));
            assert!(returned.owns_imported_population_member(&at(0)));
            assert_eq!(
                returned.observe_symbolic(&scope).unwrap().delta,
                size as i32 - 1
            );
        });
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 80 * index, "{samples:?}");
    }
}

#[test]
fn wildcard_helper_birth_does_not_scan_unrelated_imports() {
    let samples = [16_u32, 64, 256, 1024].map(|size| {
        let (scope, member) = opaque_scope(0);
        let mut entry = CreationEvents::new()
            .import_opaque_wildcard_authority(&scope)
            .unwrap();
        for index in 1..=size {
            entry = entry
                .import_opaque_wildcard_authority(&opaque_scope(index).0)
                .unwrap();
        }
        let bounded = PureFactContext::new().assume_condition(
            crate::kernel::ConditionTerm::signed_add_overflows(
                entry.observe_symbolic(&scope).unwrap().entry_count,
                Bitvector32Term::Constant(1),
            ),
            false,
        );
        let (issued, work) = crate::persistent::measure_persistent_work(|| {
            entry
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &member,
                    true,
                    &Bitvector32Term::Constant(1),
                    &bounded,
                )
                .unwrap()
                .0
        });
        assert_eq!(issued.observe_symbolic(&scope).unwrap().delta, 1);
        assert_eq!(
            issued.observe_symbolic(&opaque_scope(1).0).unwrap().delta,
            0
        );
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 32 * index, "{samples:?}");
    }
}

#[test]
fn exact_count_lookup_and_update_do_not_scan_neighboring_members() {
    let samples = [16, 64, 256].map(|size| {
        let pool = PointerBlock::Heap(950_003);
        let scope = scope(&pool, 2);
        let (mut events, _) = CreationEvents::new()
            .created(pool.clone())
            .checked_establish(&pool, &scope)
            .unwrap();
        for index in 0..size {
            events = events
                .checked_member_exchange(&pool, &description(&pool, &[index]), true)
                .unwrap()
                .0;
        }
        let selected = description(&pool, &[0]);
        let (_, work) = crate::persistent::measure_persistent_work(|| {
            assert_eq!(
                events
                    .observe_exact_member(&selected, &PureFactContext::new())
                    .unwrap()
                    .entry_count,
                Bitvector32Term::Constant(1)
            );
            let (spent, _) = events
                .checked_member_exchange(&pool, &selected, false)
                .unwrap();
            assert_eq!(
                spent
                    .observe_exact_member(&selected, &PureFactContext::new())
                    .unwrap()
                    .entry_count,
                Bitvector32Term::Constant(0)
            );
        });
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 64 * index, "{samples:?}");
    }
}

#[test]
fn wildcard_scope_lookup_and_exchange_ignore_unrelated_pools() {
    let samples = [16_u64, 64, 256, 1024].map(|size| {
        let pool = PointerBlock::Heap(930_000);
        let mut events = CreationEvents::new().created(pool.clone());
        events = events.checked_establish(&pool, &scope(&pool, 2)).unwrap().0;
        for index in 1..=size {
            let other = PointerBlock::Heap(930_000 + index);
            events = events
                .created(other.clone())
                .checked_establish(&other, &scope(&other, 2))
                .unwrap()
                .0;
        }
        let member = description(&pool, &[1]);
        let ((next, _), work) = crate::instrumentation::measure_deterministic_work(|| {
            events
                .checked_member_exchange(&pool, &member, true)
                .unwrap()
        });
        assert_eq!(
            next.observe_term(&pool, "slot").unwrap(),
            Bitvector32Term::Constant(1)
        );
        assert_eq!(
            next.observe_term(&PointerBlock::Heap(930_001), "slot")
                .unwrap(),
            Bitvector32Term::Constant(0)
        );
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 8 * index, "{samples:?}");
    }
}
