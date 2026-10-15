// Scaling tests of `src/kernel/fold_read_summary/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn summary_checking_is_linear_in_the_definition_body() {
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let step = (1..size).fold(counted(read_at(item()), int(1), int(0)), |step, _| {
            SpecIntegerExpression::Add(
                Box::new(step),
                Box::new(counted(read_at(item()), int(1), int(0))),
            )
        });
        let body = fold(name("lo"), name("hi"), zero(), step);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| check(body.clone()));
        result.expect("a long body of exact reads is in the subset");
        samples.push((size, work));
    }
    assert_linear("fold read summary check over body size", &samples);
}

#[test]
fn framing_is_linear_in_applications_and_ignores_unrelated_facts_and_interval_length() {
    // Number of applications: one conjunction of `size` framed equalities.
    let mut samples = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let after = before.clone().store(element(&v, bv(HI)), one());
        let at = |memory: &CMemory, index: usize| {
            fact(ConditionTerm::IntegerEqual(
                IntegerTerm::PureFunctionApplication(application(
                    memory,
                    &v,
                    bv(10_000 + index as u32),
                    bv(HI),
                ))
                .into(),
                IntegerTerm::constant_i64(0).into(),
            ))
        };
        let conjunction = |memory: &CMemory| {
            (1..size).fold(at(memory, 0), |all, index| {
                Proposition::And(Box::new(all), Box::new(at(memory, index)))
            })
        };
        let (source, target) = (conjunction(&before), conjunction(&after));
        let facts = PureFactContext::new();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_application_transport(&source, &target, &facts)
        });
        assert_eq!(
            result
                .expect("every application is framed")
                .framed_applications,
            size
        );
        samples.push((size, work));
    }
    assert_linear("fold framing over application count", &samples);

    // Unrelated facts: one framing whose bound is an exact fact, beside a
    // growing number of unrelated order facts.
    let mut works = Vec::new();
    for size in [64usize, 128, 256, 512] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let after = before.clone().store(element(&v, bv(J)), one());
        let old = application(&before, &v, bv(LO), bv(HI));
        let new = application(&after, &v, bv(LO), bv(HI));
        let mut facts = vec![lt(bv(J), bv(LO))];
        for index in 0..size as u32 {
            facts.push(lt(bv(20_000 + index), bv(30_000 + index)));
        }
        let facts = context(&facts);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_applications(&old, &new, &facts)
        });
        assert_eq!(result, Ok(1));
        works.push((size, work));
    }
    eprintln!("fold framing beside unrelated facts (facts, units): {works:?}");
    assert!(
        works.iter().all(|(_, work)| *work == works[0].1),
        "framing work must not depend on unrelated facts: {works:?}"
    );

    // Numeric interval length: `[0, 10)` and `[0, 1_000_000_000)` cost the
    // same, because no step enumerates the range.
    let mut lengths = Vec::new();
    for length in [10u32, 1_000, 1_000_000, 1_000_000_000] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let before = CMemory::new();
        let end = Bitvector32Term::Constant(length);
        let after = before.clone().store(element(&v, end.clone()), one());
        let old = application(&before, &v, Bitvector32Term::Constant(0), end.clone());
        let new = application(&after, &v, Bitvector32Term::Constant(0), end);
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| frame(&old, &new, &[]));
        assert_eq!(result, Ok(1));
        lengths.push((length as usize, work));
    }
    eprintln!("fold framing over interval length (length, units): {lengths:?}");
    assert!(
        lengths.iter().all(|(_, work)| *work == lengths[0].1),
        "framing work must not depend on the numeric interval length: {lengths:?}"
    );
}

#[test]
fn repeated_framing_along_a_store_sequence_is_linear() {
    // A straight line of `size` stores above the prefix, with the prefix's
    // application checked across each store in turn: one step each, so the
    // whole sequence is linear rather than a quadratic history walk.
    let mut stepwise = Vec::new();
    let mut whole = Vec::new();
    for size in [16usize, 32, 64, 128] {
        let _session = VerificationSession::enter();
        register_unmarked();
        let v = parameter_base(V);
        let mut memories = vec![CMemory::new()];
        let mut facts = Vec::new();
        for index in 0..size as u32 {
            let written = bv(40_000 + index);
            facts.push(le(bv(HI), written.clone()));
            let next = memories
                .last()
                .unwrap()
                .clone()
                .store(element(&v, written), one());
            memories.push(next);
        }
        let facts = context(&facts);
        let applications = memories
            .iter()
            .map(|memory| application(memory, &v, Bitvector32Term::Constant(0), bv(HI)))
            .collect::<Vec<_>>();
        let (crossed, work) = crate::instrumentation::measure_deterministic_work(|| {
            applications
                .windows(2)
                .map(|pair| frame_fold_applications(&pair[0], &pair[1], &facts).unwrap())
                .sum::<usize>()
        });
        assert_eq!(crossed, size);
        stepwise.push((size, work));
        let (crossed, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_fold_applications(&applications[0], applications.last().unwrap(), &facts).unwrap()
        });
        assert_eq!(crossed, size);
        whole.push((size, work));
    }
    assert_linear("fold framing across each store of a sequence", &stepwise);
    assert_linear("fold framing across a whole store sequence", &whole);
}
