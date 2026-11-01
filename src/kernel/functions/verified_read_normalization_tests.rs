use super::*;

#[test]
fn verified_read_ensure_normalization_preserves_snapshot_and_load_type() {
    let pointer = Pointer {
        block: "local:verified-read".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block(pointer.block.clone(), 4)
        .store(pointer.clone(), crate::kernel::uint8(3u32));
    let after = before
        .clone()
        .store(pointer.clone(), crate::kernel::uint8(9u32));
    let unknown = CMemory::new().with_block(pointer.block.clone(), 4);
    for (memory, kind, expected) in [
        (&before, LoadKind::UInt8, Some(3)),
        (&after, LoadKind::UInt8, Some(9)),
        (&before, LoadKind::Int32, None),
        (&unknown, LoadKind::UInt8, None),
        (&before, LoadKind::UInt8, Some(3)),
    ] {
        let load = Bitvector32Term::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &intern_c_memory_ref(memory),
            &pointer,
            kind,
            kind.byte_width(),
        ));
        let result = Bitvector32Term::Variable(Variable(930_401));
        // A byte read is an 8-bit value, compared at its own format.
        let equal = |left: Bitvector32Term, right: Bitvector32Term| match kind {
            LoadKind::UInt8 => ConditionTerm::narrow_compare(
                crate::kernel::MachineIntegerType::UInt8,
                crate::kernel::CompareRelation::Equal,
                left,
                right,
            ),
            _ => ConditionTerm::equal(left, right),
        };
        let ensure = Proposition::ConditionIs(equal(result.clone(), load), true);
        let mut facts = crate::kernel::ExecutionFacts::new();
        add_normalized_verified_ensure_facts(
            &mut facts,
            &ensure,
            &PureFactContext::new(),
            &[],
            &[],
        );
        if let Some(value) = expected {
            let expected = Proposition::ConditionIs(
                equal(
                    result,
                    Bitvector32Term::narrow_constant(
                        crate::kernel::MachineIntegerType::UInt8,
                        value,
                    ),
                ),
                true,
            );
            assert!(facts.iter().any(|fact| fact.proposition() == &expected));
        } else {
            assert!(facts.is_empty());
        }
    }
}
