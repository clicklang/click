use super::*;

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Pointer {
    Pointer {
        block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn argument(pointer: Pointer) -> PureFunctionArgument {
    PureFunctionArgument::Value(CValue::typed_pointer(pointer, CType::Int32Pointer))
}

#[test]
fn pure_pointer_calls_preserve_identity_and_do_not_imply_separation() {
    let p = Pointer::symbolic(Variable(410));
    let q = Pointer::symbolic(Variable(411));
    let a = call("select", vec![argument(p.clone())]);
    let b = call("select", vec![argument(q)]);
    assert_eq!(a, call("select", vec![argument(p)]));
    assert_ne!(a, b);
    assert!(!a.blocks_proven_distinct(&b));
    let heap = Pointer {
        block: PointerBlock::Heap(55),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(!a.blocks_proven_distinct(&heap));
    assert!(!heap.blocks_proven_distinct(&a));
    assert_ne!(a, call("different", vec![]));
}

#[test]
fn pure_pointer_rewrite_preserves_offsets_and_distinct_arguments() {
    let p = Pointer::symbolic(Variable(410));
    let q = Pointer::symbolic(Variable(411));
    let mut input = call("select", vec![argument(p.clone()), argument(q.clone())]);
    input.offset = PointerOffsetTerm::Constant(8);
    let replacement = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let mut expected = call("select", vec![argument(replacement.clone()), argument(q)]);
    expected.offset = input.offset.clone();
    let mut rewrite = TermRewrite::for_pointer_variable(Variable(410), &replacement);
    assert_eq!(rewrite.pointer(&input), expected);
    assert_eq!(rewrite.refusal(), None);
}

#[test]
fn pure_pointer_arguments_respect_match_binders_and_avoid_capture() {
    let bound = Variable(500);
    let free = Variable(501);
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
    }]
    .into();
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "PointerScope".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "PointerScope".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let input = Bitvector32Term::AlgebraicMatch {
        scrutinee: Box::new(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(502)),
        }),
        arms: vec![AlgebraicBitvectorMatchArm {
            binding_names: Default::default(),
            variant: "Node".into(),
            bindings: vec![AlgebraicValue::C(CValue::typed_pointer(
                Pointer::symbolic(bound),
                CType::Int32Pointer,
            ))],
            body: Bitvector32Term::ClickFunctionApplication {
                name: "observe".into(),
                arguments: vec![argument(call(
                    "select",
                    vec![
                        argument(Pointer::symbolic(bound)),
                        argument(Pointer::symbolic(free)),
                    ],
                ))],
            },
        }],
    };
    let replacement = call("replacement", vec![argument(Pointer::symbolic(bound))]);
    let mut rewrite = TermRewrite::for_pointer_variable(free, &replacement);
    let Bitvector32Term::AlgebraicMatch { arms, .. } = rewrite.bits(&input) else {
        panic!("lost match")
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::C(CValue::Pointer(renamed)) = &arms[0].bindings[0] else {
        panic!("lost binder")
    };
    assert_ne!(renamed.pointer(), &Pointer::symbolic(bound));
    let expected = Bitvector32Term::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(call(
            "select",
            vec![
                argument(renamed.pointer().clone()),
                argument(replacement.clone()),
            ],
        ))],
    };
    assert_eq!(arms[0].body, expected);
    let unrelated = Pointer::symbolic(Variable(503));
    let mut shadowed = TermRewrite::for_pointer_variable(bound, &unrelated);
    assert_eq!(shadowed.bits(&input), input);
    assert_eq!(shadowed.refusal(), None);

    let source = Pointer::symbolic(free);
    let mut exact = TermRewrite::for_pointer_exact(&source, &replacement);
    let _ = exact.bits(&input);
    assert_eq!(exact.refusal(), Some(RewriteRefusal::UnsupportedScope));
}

#[test]
fn pure_pointer_capture_cache_does_not_hide_a_free_occurrence_after_a_fold() {
    let item = Variable(610);
    let application = call(
        "select",
        vec![PureFunctionArgument::Value(CValue::Int32(
            Bitvector32Term::Variable(item),
        ))],
    );
    let observed = Bitvector32Term::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(application)],
    };
    let fold = Bitvector32Term::RangeFold {
        start: Box::new(Bitvector32Term::Constant(0)),
        end: Box::new(Bitvector32Term::Constant(4)),
        initial: Box::new(Bitvector32Term::Constant(0)),
        accumulator: Variable(611),
        item,
        body: Box::new(observed.clone()),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(fold), Box::new(observed)),
        true,
    );
    let mut variables = BTreeSet::new();
    crate::kernel::prelude::collect_proposition_capture_variables(&proposition, &mut variables);
    assert!(
        variables.contains(&item),
        "the right occurrence is outside the fold's binder"
    );
}

#[test]
fn pure_pointer_projection_does_not_replace_a_program_spelling() {
    let program = Pointer::symbolic(Variable(410));
    let binding = Pointer::symbolic(Variable(411));
    let projection = call("select", vec![argument(binding.clone())]);
    let equality = |a, b| Proposition::ConditionIs(ConditionTerm::pointer_equal(a, b), true);
    let projection_only =
        PureFactContext::new().assume_proposition(equality(binding.clone(), projection));
    let value = CValue::typed_pointer(binding.clone(), CType::Int32Pointer);
    assert_eq!(
        crate::kernel::arm_binding_program_spelling(&value, &projection_only),
        None
    );
    let with_program = projection_only.assume_proposition(equality(binding, program.clone()));
    assert_eq!(
        crate::kernel::arm_binding_program_spelling(&value, &with_program),
        Some(CValue::Pointer(
            CPointerValue::new(Pointer::symbolic(Variable(411)), CType::Int32Pointer)
                .with_address(program)
        )),
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/pointer_application_tests.rs");
}

#[test]
fn numeric_pointer_rewrites_preserve_origin_and_selected_extent() {
    let source = Pointer::symbolic(Variable(420));
    let target = Pointer {
        block: "target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let original = CPointerValue::new(source.clone(), CType::Int32Pointer).with_extent(Some(
        SubobjectExtent {
            start: source.clone(),
            width: 4u32.into(),
        },
    ));
    for mut rewrite in [
        TermRewrite::for_pointer_address_variable(Variable(420), &target),
        TermRewrite::for_pointer_exact(&source, &target),
    ] {
        let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(original.clone())) else {
            panic!("pointer rewrite changed the value's type")
        };
        assert_eq!(result.pointer(), &target);
        assert_eq!(result.designation(), original.designation());
        assert_eq!(result.opaque_extent(), original.opaque_extent());
        assert_eq!(result.extent().unwrap().width, 4u32.into());
        assert_eq!(result.extent().unwrap().start, target);
        assert_ne!(
            result,
            CPointerValue::new(target.clone(), CType::Int32Pointer)
        );
    }
}

#[test]
fn full_pointer_rewrite_changes_read_storage_without_inventing_its_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_c_memory(CMemory::new());
    let p = CPointerValue::new(Pointer::symbolic(Variable(421)), CType::Int32Pointer);
    let q = CPointerValue::new(Pointer::symbolic(Variable(422)), CType::Int32Pointer);
    let other = Pointer::symbolic(Variable(423));
    let read = CPointerValue::from_read(other.clone(), CType::Int32Pointer, &memory, p.pointer());
    let mut rewrite = TermRewrite::for_pointer_value_exact(&p, &q);
    let CValue::Pointer(changed) = rewrite.value(&CValue::Pointer(read.clone())) else {
        panic!("read changed type")
    };
    let expected_origin = Pointer::loaded_value(&memory, q.pointer());
    assert_eq!(changed.pointer(), &other);
    assert_eq!(changed.designation(), &expected_origin);
    assert_eq!(changed.opaque_extent(), Some(&expected_origin));
    // The same address-only rewrite cannot substitute a read's full value.
    let mut numeric = TermRewrite::for_pointer_exact(p.pointer(), q.pointer());
    assert_eq!(
        numeric.value(&CValue::Pointer(read.clone())),
        CValue::Pointer(read)
    );
    // Matching the pointee address does not match the read's storage cell.
    let read = CPointerValue::from_read(p.pointer().clone(), CType::Int32Pointer, &memory, &other);
    let mut rewrite = TermRewrite::for_pointer_value_exact(&p, &q);
    assert_eq!(
        rewrite.value(&CValue::Pointer(read.clone())),
        CValue::Pointer(read.with_address(q.pointer().clone())),
    );
}

#[test]
fn memory_relationship_rewrite_transports_only_a_complete_pointer_carrier() {
    let _session = crate::kernel::VerificationSession::enter();
    let snapshot = intern_c_memory(CMemory::new());
    let storage = Pointer::symbolic(Variable(424_100));
    let source = CPointerValue::from_read(
        Pointer::symbolic(Variable(424_101)),
        CType::Int32Pointer,
        &snapshot,
        &storage,
    );
    let target_base = Pointer {
        block: PointerBlock::Heap(424_102),
        offset: PointerOffsetTerm::Constant(0),
    };
    let target = CPointerValue::new(target_base.clone(), CType::Int32Pointer).with_extent(Some(
        SubobjectExtent {
            start: target_base,
            width: 4u32.into(),
        },
    ));
    let relationship = |value: &CPointerValue| Proposition::CResourceContains {
        parent: Box::new(CResource::Composite {
            name: "holder".into(),
            arguments: vec![AlgebraicValue::C(CValue::Pointer(value.clone()))].into(),
        }),
        child: Box::new(CResource::Memory(CMemoryRange::from_pointer_value(
            value,
            0u32.into(),
            1u32.into(),
            4,
        ))),
    };
    let input = relationship(&source);
    let mut full = TermRewrite::for_pointer_value_exact(&source, &target);
    assert_eq!(full.proposition(&input), relationship(&target));
    assert!(full.refusal().is_none());
    let mut numeric = TermRewrite::for_pointer_exact(source.pointer(), target.pointer());
    let rewritten = numeric.proposition(&input);
    let Proposition::CResourceContains { child, .. } = rewritten else {
        panic!("containment")
    };
    let CResource::Memory(range) = child.as_ref() else {
        panic!("memory")
    };
    assert_eq!(range.base(), target.pointer());
    assert_eq!(range.designation.as_ref(), source.designation());
    assert_eq!(range.opaque_extent.as_deref(), source.opaque_extent());
    assert!(!range.carrier_extent_known);
}

#[test]
fn a_full_pointer_rewrite_does_not_adopt_another_read_carrier_at_the_same_address() {
    let _session = crate::kernel::VerificationSession::enter();
    let snapshot = intern_c_memory(CMemory::new());
    let raw = Pointer::symbolic(Variable(424_110));
    let source = CPointerValue::from_read(
        raw.clone(),
        CType::Int32Pointer,
        &snapshot,
        &Pointer::symbolic(Variable(424_111)),
    );
    let unrelated = CPointerValue::from_read(
        raw,
        CType::Int32Pointer,
        &snapshot,
        &Pointer::symbolic(Variable(424_112)),
    );
    let target = CPointerValue::new(
        Pointer {
            block: PointerBlock::Heap(424_113),
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::Int32Pointer,
    );
    let input = Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::from_pointer_value(
            &unrelated,
            0u32.into(),
            1u32.into(),
            4,
        ))),
        right: Box::new(CResource::Memory(CMemoryRange::new(
            Pointer::symbolic(Variable(424_114)),
            0u32.into(),
            1u32.into(),
        ))),
    };
    let mut rewrite = TermRewrite::for_pointer_value_exact(&source, &target);
    let Proposition::CResourceSeparate { left, .. } = rewrite.proposition(&input) else {
        panic!("separation")
    };
    let CResource::Memory(range) = left.as_ref() else {
        panic!("memory")
    };
    assert_eq!(range.base(), target.pointer());
    assert_eq!(range.designation.as_ref(), unrelated.designation());
    assert_eq!(range.opaque_extent.as_deref(), unrelated.opaque_extent());
    assert!(!range.carrier_extent_known);
}

#[test]
fn full_c_argument_pointer_rewrite_reaches_a_displaced_copy() {
    let parameter = |id| {
        CPointerValue::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 1),
            },
            CType::UInt8Pointer,
        )
    };
    let base = parameter(916_201);
    let middle = parameter(916_202);
    let replacement = base.clone().with_address(base.pointer().offset_by_bytes(2));
    let displaced = middle
        .clone()
        .with_address(middle.pointer().offset_by_bytes(3));
    let mut rewrite = TermRewrite::for_pointer_value_exact(&middle, &replacement);
    let CValue::Pointer(actual) = rewrite.value(&CValue::Pointer(displaced)) else {
        panic!("pointer rewrite changed type")
    };
    let expected = base.pointer().offset_by_bytes(5);
    assert_eq!(actual.pointer().block, expected.block);
    assert_eq!(
        crate::kernel::eval::canonical_offset_term(&actual.pointer().offset),
        crate::kernel::eval::canonical_offset_term(&expected.offset)
    );
    assert_eq!(actual.designation(), base.designation());
    assert_eq!(actual.opaque_extent(), base.opaque_extent());

    let mut numeric = TermRewrite::for_pointer_exact(middle.pointer(), replacement.pointer());
    let CValue::Pointer(address_only) = numeric.value(&CValue::Pointer(middle.clone())) else {
        panic!("address rewrite changed type")
    };
    assert_eq!(address_only.designation(), middle.designation());
    assert_eq!(address_only.opaque_extent(), middle.opaque_extent());
}

#[test]
fn displaced_symbolic_pointer_rewrite_keeps_selected_bounds() {
    let source = CPointerValue::new(Pointer::symbolic(Variable(916_211)), CType::UInt8Pointer);
    let target_address = Pointer::symbolic(Variable(916_212));
    let target = CPointerValue::new(target_address.clone(), CType::UInt8Pointer).with_extent(Some(
        SubobjectExtent {
            start: target_address.clone(),
            width: 4u32.into(),
        },
    ));
    let shifted = source
        .clone()
        .with_address(source.pointer().offset_by_bytes(1));
    let CValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&CValue::Pointer(shifted))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.pointer(), &target_address.offset_by_bytes(1));
    assert_eq!(actual.designation(), target.designation());
    assert_eq!(actual.opaque_extent(), target.opaque_extent());
    assert_eq!(actual.extent(), target.extent());

    let selected = source
        .clone()
        .with_extent(Some(SubobjectExtent {
            start: source.pointer().offset_by_bytes(1),
            width: 1u32.into(),
        }))
        .with_address(source.pointer().offset_by_bytes(1));
    let CValue::Pointer(narrowed) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&CValue::Pointer(selected))
    else {
        panic!("selected pointer type")
    };
    assert_eq!(
        narrowed.extent(),
        Some(&SubobjectExtent {
            start: target_address.offset_by_bytes(1),
            width: 1u32.into(),
        })
    );

    let CValue::Pointer(numeric) =
        TermRewrite::for_pointer_exact(source.pointer(), target.pointer())
            .value(&CValue::Pointer(source.clone()))
    else {
        panic!("numeric pointer type")
    };
    assert_eq!(numeric.designation(), source.designation());
    assert_eq!(numeric.opaque_extent(), source.opaque_extent());
    assert_eq!(numeric.extent(), source.extent());
}

#[test]
fn displaced_c_argument_rewrite_inherits_known_replacement_bounds() {
    let parameter = |id| {
        CPointerValue::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(id)), 1),
            },
            CType::UInt8Pointer,
        )
    };
    let source = parameter(916_241);
    let base = parameter(916_242);
    let target = base.clone().with_extent(Some(SubobjectExtent {
        start: base.pointer().clone(),
        width: 4u32.into(),
    }));
    let input = source
        .clone()
        .with_address(source.pointer().offset_by_bytes(1));
    let CValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&CValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.extent(), target.extent());
    assert_eq!(actual.extent_is_known(), target.extent_is_known());
    assert_eq!(actual.opaque_extent(), target.opaque_extent());
}

#[test]
fn displaced_original_pointer_keeps_its_bounds_beside_a_view_equality() {
    let original = CPointerValue::new(Pointer::symbolic(Variable(916_251)), CType::UInt8Pointer);
    let other = CPointerValue::new(Pointer::symbolic(Variable(916_252)), CType::UInt8Pointer);
    let source_view = original
        .clone()
        .with_type(CType::VoidPointer)
        .with_opaque_extent(None);
    let target_view = other
        .clone()
        .with_type(CType::VoidPointer)
        .with_opaque_extent(None);
    let input = original
        .clone()
        .with_address(original.pointer().offset_by_bytes(3));
    let CValue::Pointer(actual) = TermRewrite::for_pointer_value_exact(&source_view, &target_view)
        .value(&CValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.pointer(), &other.pointer().offset_by_bytes(3));
    assert_eq!(actual.c_type(), original.c_type());
    assert_eq!(actual.opaque_extent(), original.opaque_extent());
    assert_eq!(actual.extent(), original.extent());
}

#[test]
fn displaced_copy_keeps_a_domain_not_named_by_the_full_equality() {
    let numeric = Pointer::symbolic(Variable(916_261));
    let original = CPointerValue::new(numeric.clone(), CType::UInt8Pointer).with_extent(Some(
        SubobjectExtent {
            start: numeric.clone(),
            width: 4u32.into(),
        },
    ));
    let memory = intern_c_memory(CMemory::new());
    let source = CPointerValue::from_read(
        numeric.clone(),
        CType::UInt8Pointer,
        &memory,
        &Pointer::symbolic(Variable(916_263)),
    );
    let target = CPointerValue::new(Pointer::symbolic(Variable(916_262)), CType::UInt8Pointer);
    let input = original.clone().with_address(numeric.offset_by_bytes(1));
    let CValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&CValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.pointer(), &target.pointer().offset_by_bytes(1));
    assert_eq!(actual.designation(), original.designation());
    assert_eq!(actual.opaque_extent(), original.opaque_extent());
    assert_eq!(
        actual.extent(),
        Some(&SubobjectExtent {
            start: target.pointer().clone(),
            width: 4u32.into(),
        })
    );
}
