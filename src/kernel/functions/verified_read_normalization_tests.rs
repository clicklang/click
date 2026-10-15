use super::*;

#[test]
fn verified_read_ensure_normalization_preserves_snapshot_and_load_type() {
    let pointer = Pointer {
        block: "local:verified-read".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block(pointer.block.clone(), 4)
        .store(pointer.clone(), CValue::UInt8(3u32.into()));
    let after = before
        .clone()
        .store(pointer.clone(), CValue::UInt8(9u32.into()));
    let unknown = CMemory::new().with_block(pointer.block.clone(), 4);
    for (memory, kind, expected) in [
        (&before, LoadKind::UInt8, Some(3)),
        (&after, LoadKind::UInt8, Some(9)),
        (&before, LoadKind::Bits32, None),
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
        let ensure = Proposition::ConditionIs(ConditionTerm::equal(result.clone(), load), true);
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
                ConditionTerm::equal(result, Bitvector32Term::Constant(value)),
                true,
            );
            assert!(facts.iter().any(|fact| fact.proposition() == &expected));
        } else {
            assert!(facts.is_empty());
        }
    }
}
