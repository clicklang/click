use super::*;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn separation_class_lookup_visits_only_the_selected_payload() {
    for aliases in [false, true] {
        for size in [16u64, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| OldAddress::symbolic(Variable(id));
            let model = pointer(9_884_001);
            let node = pointer(9_884_002);
            let program = OldAddress {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::scale_int32(
                    OldMachineTerm::Variable(Variable(9_884_003)),
                    4,
                ),
            };
            let separation = |left, right| Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                    left,
                    0u32.into(),
                    8u32.into(),
                    1,
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
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
                        OldConditionTerm::address_equal(model.clone(), pointer(9_886_000 + index)),
                        true,
                    );
                }
            }
            let selected = separation(model.offset_by_bytes(8), node.offset_by_bytes(16));
            context = context.assume_proposition(selected.clone());
            context = context.assume_condition(
                OldConditionTerm::address_equal(model, program.clone()),
                true,
            );
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

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 512 related separation spans and alias history"]
fn exact_separation_lookup_ignores_related_widths_and_alias_history() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| OldAddress::symbolic(Variable(id));
        let model = pointer(9_940_001);
        let source = pointer(9_940_002);
        let copied = pointer(9_940_003);
        let range = |p, n: u32| {
            Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                n.into(),
                1,
            ))
        };
        let separated = |a, an, b, bn| Proposition::ResourceSeparate {
            left: Box::new(range(a, an)),
            right: Box::new(range(b, bn)),
        };
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_proposition(separated(
                pointer(9_941_000 + i * 2),
                1,
                pointer(9_941_001 + i * 2),
                4,
            ));
            context = context.assume_proposition(separated(
                model.clone(),
                i as u32 + 2,
                source.clone(),
                i as u32 + 5,
            ));
            context = context.assume_condition(
                OldConditionTerm::address_equal(model.clone(), pointer(9_943_000 + i)),
                true,
            );
        }
        context = context.assume_proposition(separated(model.clone(), 1, source.clone(), 4));
        let branch = context
            .clone()
            .assume_condition(OldConditionTerm::address_equal(copied.clone(), model), true);
        let before = SOURCE_VISITS.with(Cell::get);
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            branch.contains_known(&Proposition::ResourceSeparate {
                left: Box::new(range(copied, 1)),
                right: Box::new(range(source, 4)),
            })
        });
        assert!(proved);
        assert_eq!(SOURCE_VISITS.with(Cell::get) - before, 1);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}

#[test]
fn symbolic_size_span_lookup_visits_only_its_authority() {
    // A whole object of abstract size is a span keyed by its size term:
    // finding its stated separation reads that one authority among many.
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |id| OldAddress::symbolic(Variable(id));
        let parameter = TypeParameterName::intern("ScaledSpanT");
        let object = |p: OldAddress| {
            Resource::Memory(MemoryRange::of_access(&p, AccessExtent::Object(parameter)))
        };
        let bytes = |p: OldAddress, n: u32| {
            Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                n.into(),
                1,
            ))
        };
        let separated = |left, right| Proposition::ResourceSeparate {
            left: Box::new(left),
            right: Box::new(right),
        };
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_proposition(separated(
                object(pointer(9_951_000 + 2 * index)),
                bytes(pointer(9_951_001 + 2 * index), 8),
            ));
        }
        let (value, header) = (pointer(9_950_001), pointer(9_950_002));
        context =
            context.assume_proposition(separated(object(value.clone()), bytes(header.clone(), 8)));
        let before = SOURCE_VISITS.with(Cell::get);
        assert!(context.contains_known(&separated(bytes(header, 8), object(value))));
        let visits = SOURCE_VISITS.with(Cell::get) - before;
        assert_eq!(visits, 1, "size={size}");
    }
}
