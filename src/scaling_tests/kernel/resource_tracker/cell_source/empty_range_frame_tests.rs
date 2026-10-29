// Deterministic work for the structurally empty typed frame rule.
use super::*;

#[test]
fn empty_range_frames_ignore_related_and_unrelated_separation_candidates() {
    for related in [false, true] {
        let mut samples = Vec::new();
        for size in [4u64, 16, 64] {
            let _session = crate::kernel::VerificationSession::enter();
            let base = Pointer::symbolic(Variable(9_952_000));
            let read = Pointer::symbolic(Variable(9_952_001));
            let bound = Bitvector32Term::Variable(Variable(9_952_002));
            let range = CMemoryRange::new(base.clone(), bound.clone(), bound);
            let mut context = PureFactContext::new();
            for index in 0..size {
                let candidate_base = if related {
                    base.clone()
                } else {
                    Pointer::symbolic(Variable(9_953_000 + index))
                };
                context = context.assume_proposition(Proposition::CResourceSeparate {
                    left: Box::new(CResource::Memory(CMemoryRange::new(
                        candidate_base,
                        ((index * 2) as u32).into(),
                        ((index * 2 + 1) as u32).into(),
                    ))),
                    right: Box::new(CResource::Memory(CMemoryRange::new(
                        read.clone(),
                        0u32.into(),
                        1u32.into(),
                    ))),
                });
            }
            let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
                typed_range_disjoint_from_pointer_evidence(&range, &read, 16, &context)
            });
            assert!(matches!(
                proof,
                Some(RangeDisjointFromPointerEvidence::Empty)
            ));
            samples.push(work);
        }
        assert_eq!(samples, vec![1, 1, 1], "related={related}");
    }
}
