// Deterministic scaling coverage for the independent designation index.
use super::*;
use crate::kernel::*;

#[test]
fn designation_queries_and_withdrawal_ignore_unrelated_origins() {
    let mut measurements = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut classes = ValueClasses::<u64>::default();
        classes.insert(&1, &2, |a, _| *a);
        classes.insert(&2, &3, |a, _| *a);
        for index in 0..size {
            classes.insert(&(10 + index * 2), &(11 + index * 2), |a, _| *a);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(classes.equal(&1, &3));
            classes.remove(&1, &2, |a, _| *a);
            assert!(!classes.equal(&1, &3));
            assert!(classes.equal(&2, &3));
        });
        measurements.push(work);
    }
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}

#[test]
fn typed_access_does_not_search_unrelated_address_equalities_or_ranges() {
    let value = |id| CPointerValue::new(Pointer::symbolic(Variable(id)), CType::Int32Pointer);
    let a = value(870_001);
    let b = value(870_002);
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        let mut resources = ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::from_pointer_value(&b, 0u32.into(), 1u32.into(), 4),
        ));
        for index in 0..size {
            let unrelated = value(880_000 + index * 2);
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    unrelated.pointer().clone(),
                    value(880_001 + index * 2).pointer().clone(),
                ),
                true,
            );
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::from_pointer_value(&unrelated, 0u32.into(), 1u32.into(), 4),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(resources.permits_designated_memory_read(
                b.pointer(),
                Some(b.access_designation()),
                4,
                &context
            ));
            assert!(!resources.permits_designated_memory_read(
                a.pointer(),
                Some(a.access_designation()),
                4,
                &context
            ));
        });
        samples.push(work);
    }
    assert!(samples[3] <= samples[0] * 4 + 32, "{samples:?}");
    {
        let costs = samples.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([4u64, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
fn pointer_integer_round_trips_ignore_unrelated_facts() {
    let pointer = CPointerValue::new(Pointer::symbolic(Variable(992_001)), CType::Int32Pointer);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    Bitvector32Term::Variable(Variable(993_000 + index)),
                    Bitvector32Term::UInt64Constant(index),
                ),
                true,
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut obligations = Vec::new();
            let word = crate::kernel::eval::cast_c_value_to_type(
                CValue::Pointer(pointer.clone()),
                CType::UInt64,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &context,
            )
            .unwrap();
            let back = crate::kernel::eval::cast_c_value_to_type(
                word,
                CType::Int32Pointer,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &context,
            )
            .unwrap();
            assert_eq!(back, CValue::Pointer(pointer.clone()));
            assert!(obligations.is_empty());
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn packed_word_contract_lookup_and_scope_ignore_unrelated_words() {
    let _session = VerificationSession::enter();
    let value = |id| CPointerValue::new(Pointer::symbolic(Variable(id)), CType::Int32Pointer);
    let equality = |a: &CPointerValue, b: &CPointerValue| {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(a.clone()), Box::new(b.clone())),
            true,
        )
    };
    let reconstructed = |id| {
        let word = CValue::UInt64(Bitvector32Term::Variable(Variable(id)))
            .complete_word(Pointer::symbolic(Variable(id + 1)));
        let value = crate::kernel::eval::cast_c_value_to_type(
            word,
            CType::Int32Pointer,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        let CValue::Pointer(pointer) = value else {
            panic!("pointer")
        };
        pointer
    };
    let source = reconstructed(998_000);
    let target = value(998_002);
    let relation = equality(&source, &target);
    let mut measurements = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut parent = PureFactContext::new();
        for index in 0..size {
            parent = parent.assume_proposition(equality(
                &reconstructed(1_000_000 + index * 4),
                &value(1_000_002 + index * 4),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!parent.pointer_designations_match(&source, &target));
            let child = parent.clone().assume_proposition(relation.clone());
            assert!(child.pointer_designations_match(&source, &target));
            let withdrawn = child.without_exact_fact(&relation);
            assert!(!withdrawn.pointer_designations_match(&source, &target));
            assert!(!parent.pointer_designations_match(&source, &target));
        });
        measurements.push(work);
    }
    eprintln!("packed-word selected work: {measurements:?}");
    assert!(
        measurements
            .iter()
            .all(|work| *work <= measurements[0] + 32),
        "{measurements:?}"
    );
}
