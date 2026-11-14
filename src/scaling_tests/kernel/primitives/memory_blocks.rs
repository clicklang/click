use super::*;

#[test]
fn scalar_declaration_and_retirement_do_not_reindex_heap_blocks() {
    let mut curves = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for index in 0..count {
            memory = memory.with_block(Pointer::symbolic(Variable(9_393_000 + index)).block, 16);
        }
        let scalar = Pointer::symbolic(Variable(9_394_000)).block;
        let mut samples = Vec::new();
        for _ in 0..3 {
            let (((declared, retired), work), maps) =
                crate::persistent::measure_persistent_work(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        let declared = memory.clone().with_declared_scalar_block(
                            scalar.clone(),
                            4,
                            ProgramType::Int32,
                        );
                        let retired = declared.without_local_block(&scalar);
                        (declared, retired)
                    })
                });
            assert_eq!(
                declared.blocks.scalar_blocks().collect::<Vec<_>>(),
                vec![&scalar]
            );
            assert_eq!(retired.blocks.scalar_blocks().count(), 0);
            assert_eq!(memory.blocks.scalar_blocks().count(), 0);
            assert_eq!(retired.blocks.len(), count as usize);
            samples.push((work, maps));
        }
        curves.push((count, samples));
    }
    assert!(
        curves[3]
            .1
            .iter()
            .zip(&curves[0].1)
            .all(|(large, small)| large.0 <= small.0 + 64 && large.1 <= small.1 * 3 + 256),
        "{curves:?}"
    );
}
