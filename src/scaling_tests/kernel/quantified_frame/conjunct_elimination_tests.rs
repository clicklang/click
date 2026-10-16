// Scaling tests of `src/kernel/quantified_frame.rs` (module `conjunct_elimination_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Carrying `defined(p[0])` out of `other and defined(p[0])` across one
/// disjoint store costs the same beside 16, 64 or 256 unrelated stores made
/// before the source snapshot and as many unrelated facts in the querying
/// context: conjunction elimination reads only the source's conjunction
/// spine, and the definedness leaf, decided here by the kernel's typed-read
/// no-write walk standing in for the single-fact route, reads only the steps
/// between its two snapshots.
#[test]
fn conjunct_elimination_is_flat_against_unrelated_history_and_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: "conjunct-frame".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Pointer {
        block: "conjunct-frame-unrelated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut costs = Vec::new();
    for size in [16u32, 64, 256] {
        let mut before = CMemory::new()
            .with_block("conjunct-frame", 16)
            .with_block("conjunct-frame-unrelated", size);
        for index in 0..size {
            before = before.store(
                unrelated.offset_by_bytes(index),
                CValue::UInt8(Bitvector32Term::Constant(index % 251)),
            );
        }
        let after = before.clone().store(
            base.offset_by_bytes(8),
            CValue::UInt8(Bitvector32Term::Constant(0)),
        );
        let assumptions = (0..size).fold(PureFactContext::new(), |context, index| {
            context.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(50_000 + u64::from(index))),
                true,
            ))
        });
        let defined = |memory: &CMemory| Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: base.clone(),
            value_type: CType::UInt8,
        };
        // Built outside the measurement: interning a snapshot is paid by
        // whoever builds it, not by the frame.
        let other = Proposition::ConditionIs(ConditionTerm::Variable(Variable(49_999)), true);
        let source = Proposition::And(Box::new(other), Box::new(defined(&before)));
        let target = defined(&after);
        let leaf =
            |from: &Proposition, to: &Proposition, context: &PureFactContext| match (from, to) {
                (
                    Proposition::CMemoryReadDefined {
                        memory: before,
                        pointer,
                        value_type,
                    },
                    Proposition::CMemoryReadDefined { memory: after, .. },
                ) => crate::kernel::memory_provenance::typed_read_has_same_memory_source(
                    before,
                    after,
                    pointer,
                    value_type.byte_width(),
                    context,
                ),
                _ => false,
            };
        let facts = ProofFacts::default();
        let same = |context: PureFactContext| context;
        let variables = BTreeSet::new();
        let (carried, work) = crate::instrumentation::measure_deterministic_work(|| {
            frame_quantified_transport(
                &source,
                &target,
                &facts,
                &assumptions,
                &assumptions,
                &leaf,
                &same,
                &variables,
            )
        });
        assert_eq!(carried, Ok(()));
        costs.push(work);
    }
    eprintln!("conjunct elimination work by size: {costs:?}");
    assert!(
        costs.windows(2).all(|pair| pair[0] == pair[1]),
        "conjunct elimination work: {costs:?}"
    );
}
