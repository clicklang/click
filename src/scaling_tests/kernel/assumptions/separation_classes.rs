use super::*;

#[test]
fn separation_class_lookup_visits_only_the_selected_payload() {
    for aliases in [false, true] {
        for size in [16u64, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer::symbolic(Variable(id));
            let model = pointer(9_884_001);
            let node = pointer(9_884_002);
            let program = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(9_884_003)),
                    4,
                ),
            };
            let separation = |left, right| Proposition::CResourceSeparate {
                left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                    left,
                    0u32.into(),
                    8u32.into(),
                    1,
                ))),
                right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                    right,
                    0u32.into(),
                    8u32.into(),
                    1,
                ))),
            };
            let mut context = PureFactContext::new();
            for index in 0..size {
                context = context.assume_proposition(separation(
                    pointer(9_885_000 + 2 * index),
                    pointer(9_885_001 + 2 * index),
                ));
                if aliases {
                    context = context.assume_condition(
                        ConditionTerm::pointer_equal(model.clone(), pointer(9_886_000 + index)),
                        true,
                    );
                }
            }
            let selected = separation(model.offset_by_bytes(8), node.offset_by_bytes(16));
            context = context.assume_proposition(selected.clone());
            context = context
                .assume_condition(ConditionTerm::pointer_equal(model, program.clone()), true);
            let before = SOURCE_VISITS.with(Cell::get);
            let candidates = context.separated_address_classes.candidates(
                &program.offset_by_bytes(8),
                &node.offset_by_bytes(16),
                &context.equality_graph,
            );
            let visits = SOURCE_VISITS.with(Cell::get) - before;
            assert_eq!(candidates, vec![selected]);
            // Only this pair can be rekeyed by the selected origin merge,
            // then the lookup reads its one authority. Unrelated separation
            // rows and the older aliases supply no candidate visits.
            assert!(
                visits <= 2,
                "size={size}, aliases={aliases}, source visits={visits}"
            );
        }
    }
}
