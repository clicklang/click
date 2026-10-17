// Scaling tests of src/kernel/equality_graph/separation_tests.rs.
use super::*;

#[test]
fn address_separation_lookup_ignores_unrelated_sources() {
    let _session = VerificationSession::enter();
    let mut costs = Vec::new();
    for size in [8u64, 32, 128, 512] {
        let (a, b, c) = (pointer(100), pointer(101), pointer(102));
        let mut context = PureFactContext::new().assume_proposition(separate(&a, &b));
        for i in 0..size {
            context = context
                .assume_proposition(separate(&pointer(1000 + 2 * i), &pointer(1001 + 2 * i)));
        }
        context.equality_graph.add_checked_read_equality(&b, &c);
        let (known, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.contains_known(&different(&a, &c))
        });
        assert!(known);
        costs.push(work);
    }
    assert!(
        costs.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "{costs:?}"
    );
}

#[test]
fn owned_address_admission_does_not_generate_pairs() {
    let _session = VerificationSession::enter();
    let mut costs = Vec::new();
    for size in [8u64, 32, 128, 512] {
        let mut owners = ResourceContext::new();
        for i in 0..size {
            owners = owners.unchecked_with_fact(CResourceFact::own_memory(range(
                &pointer(3000 + i),
                0,
                1,
            )));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            PureFactContext::new().assume_proposition(Proposition::CResourceComposition(owners))
        });
        costs.push((size, work));
    }
    for pair in costs.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) as usize * 2,
            "{costs:?}"
        );
    }
}
