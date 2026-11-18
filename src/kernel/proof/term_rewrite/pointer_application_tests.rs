use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Address {
    Address {
        base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: AddressOffset::Constant(0),
    }
}
fn argument(pointer: Address) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::typed_pointer(
        pointer,
        ProgramType::Int32Pointer,
    ))
}

#[test]
fn pure_pointer_calls_preserve_identity_and_do_not_imply_separation() {
    let p = Address::symbolic(Variable(410));
    let q = Address::symbolic(Variable(411));
    let a = call("select", vec![argument(p.clone())]);
    let b = call("select", vec![argument(q)]);
    assert_eq!(a, call("select", vec![argument(p)]));
    assert_ne!(a, b);
    assert!(!a.blocks_proven_distinct(&b));
    let heap = Address {
        base: AddressBase::Heap(55),
        offset: AddressOffset::Constant(0),
    };
    assert!(!a.blocks_proven_distinct(&heap));
    assert!(!heap.blocks_proven_distinct(&a));
    assert_ne!(a, call("different", vec![]));
}

#[test]
fn pure_pointer_rewrite_preserves_offsets_and_distinct_arguments() {
    let p = Address::symbolic(Variable(410));
    let q = Address::symbolic(Variable(411));
    let mut input = call("select", vec![argument(p.clone()), argument(q.clone())]);
    input.offset = AddressOffset::Constant(8);
    let replacement = Address {
        base: "target".into(),
        offset: AddressOffset::Constant(4),
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
        fields: vec![AlgebraicValueType::Program(ProgramType::Int32Pointer)],
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
    let input = MachineTerm::AlgebraicMatch {
        scrutinee: Box::new(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(502)),
        }),
        arms: vec![AlgebraicBitvectorMatchArm {
            binding_names: Default::default(),
            variant: "Node".into(),
            bindings: vec![AlgebraicValue::Program(ProgramValue::typed_pointer(
                Address::symbolic(bound),
                ProgramType::Int32Pointer,
            ))],
            body: MachineTerm::ClickFunctionApplication {
                name: "observe".into(),
                arguments: vec![argument(call(
                    "select",
                    vec![
                        argument(Address::symbolic(bound)),
                        argument(Address::symbolic(free)),
                    ],
                ))],
            },
        }],
    };
    let replacement = call("replacement", vec![argument(Address::symbolic(bound))]);
    let mut rewrite = TermRewrite::for_pointer_variable(free, &replacement);
    let MachineTerm::AlgebraicMatch { arms, .. } = rewrite.bits(&input) else {
        panic!("lost match")
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::Program(ProgramValue::Pointer(renamed)) = &arms[0].bindings[0] else {
        panic!("lost binder")
    };
    assert_ne!(renamed.address(), &Address::symbolic(bound));
    let expected = MachineTerm::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(call(
            "select",
            vec![
                argument(renamed.address().clone()),
                argument(replacement.clone()),
            ],
        ))],
    };
    assert_eq!(arms[0].body, expected);
    let unrelated = Address::symbolic(Variable(503));
    let mut shadowed = TermRewrite::for_pointer_variable(bound, &unrelated);
    assert_eq!(shadowed.bits(&input), input);
    assert_eq!(shadowed.refusal(), None);

    let source = Address::symbolic(free);
    let mut exact = TermRewrite::for_pointer_exact(&source, &replacement);
    let _ = exact.bits(&input);
    assert_eq!(exact.refusal(), Some(RewriteRefusal::UnsupportedScope));
}

#[test]
fn pure_pointer_capture_cache_does_not_hide_a_free_occurrence_after_a_fold() {
    let item = Variable(610);
    let application = call(
        "select",
        vec![PureFunctionArgument::Value(ProgramValue::Int32(
            MachineTerm::Variable(item),
        ))],
    );
    let observed = MachineTerm::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(application)],
    };
    let fold = MachineTerm::RangeFold {
        start: Box::new(MachineTerm::constant(0)),
        end: Box::new(MachineTerm::constant(4)),
        initial: Box::new(MachineTerm::constant(0)),
        accumulator: Variable(611),
        item,
        body: Box::new(observed.clone()),
    };
    let proposition = Proposition::condition_is(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(fold),
            right: Box::new(observed),
        },
        true,
    );
    let mut variables = BTreeSet::new();
    crate::kernel::prelude::collect_proposition_capture_variables(&proposition, &mut variables);
    assert!(
        variables.contains(&item),
        "the right occurrence is outside the fold's binder"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/term_rewrite/pointer_application_tests.rs");
}

#[test]
fn numeric_pointer_rewrites_preserve_origin_and_selected_bounds() {
    let source = Address::symbolic(Variable(420));
    let target = Address {
        base: "target".into(),
        offset: AddressOffset::Constant(0),
    };
    let original = Pointer::new(source.clone(), ProgramType::Int32Pointer).with_bounds(Some(
        SubobjectBounds {
            start: source.clone(),
            width: 4u32.into(),
        },
    ));
    for mut rewrite in [
        TermRewrite::for_pointer_address_variable(Variable(420), &target),
        TermRewrite::for_pointer_exact(&source, &target),
    ] {
        let ProgramValue::Pointer(result) = rewrite.value(&ProgramValue::Pointer(original.clone()))
        else {
            panic!("pointer rewrite changed the value's type")
        };
        assert_eq!(result.address(), &target);
        assert_eq!(result.provenance(), original.provenance());
        assert_eq!(result.bounds_owner(), original.bounds_owner());
        assert_eq!(result.bounds().unwrap().width, 4u32.into());
        assert_eq!(result.bounds().unwrap().start, target);
        assert_ne!(
            result,
            Pointer::new(target.clone(), ProgramType::Int32Pointer)
        );
    }
}

#[test]
fn full_pointer_rewrite_changes_read_storage_without_inventing_its_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(SymbolicMemory::new());
    let p = Pointer::new(Address::symbolic(Variable(421)), ProgramType::Int32Pointer);
    let q = Pointer::new(Address::symbolic(Variable(422)), ProgramType::Int32Pointer);
    let other = Address::symbolic(Variable(423));
    let read = Pointer::from_read(
        other.clone(),
        ProgramType::Int32Pointer,
        &memory,
        p.address(),
    );
    let mut rewrite = TermRewrite::for_pointer_value_exact(&p, &q);
    let ProgramValue::Pointer(changed) = rewrite.value(&ProgramValue::Pointer(read.clone())) else {
        panic!("read changed type")
    };
    let expected_origin = Address::loaded_value(&memory, q.address());
    assert_eq!(changed.address(), &other);
    assert_eq!(changed.provenance(), &expected_origin);
    assert_eq!(changed.bounds_owner(), Some(&expected_origin));
    // The same address-only rewrite cannot substitute a read's full value.
    let mut numeric = TermRewrite::for_pointer_exact(p.address(), q.address());
    assert_eq!(
        numeric.value(&ProgramValue::Pointer(read.clone())),
        ProgramValue::Pointer(read)
    );
    // Matching the pointee address does not match the read's storage cell.
    let read = Pointer::from_read(
        p.address().clone(),
        ProgramType::Int32Pointer,
        &memory,
        &other,
    );
    let mut rewrite = TermRewrite::for_pointer_value_exact(&p, &q);
    assert_eq!(
        rewrite.value(&ProgramValue::Pointer(read.clone())),
        ProgramValue::Pointer(read.with_address(q.address().clone())),
    );
}

#[test]
fn memory_relationship_rewrite_transports_only_a_complete_pointer_carrier() {
    let _session = crate::kernel::VerificationSession::enter();
    let retained_state = intern_memory(SymbolicMemory::new());
    let storage = Address::symbolic(Variable(424_100));
    let source = Pointer::from_read(
        Address::symbolic(Variable(424_101)),
        ProgramType::Int32Pointer,
        &retained_state,
        &storage,
    );
    let target_base = Address {
        base: AddressBase::Heap(424_102),
        offset: AddressOffset::Constant(0),
    };
    let target = Pointer::new(target_base.clone(), ProgramType::Int32Pointer).with_bounds(Some(
        SubobjectBounds {
            start: target_base,
            width: 4u32.into(),
        },
    ));
    let relationship = |value: &Pointer| Proposition::ResourceContains {
        parent: Box::new(Resource::Composite {
            name: "holder".into(),
            arguments: vec![AlgebraicValue::Program(ProgramValue::Pointer(
                value.clone(),
            ))]
            .into(),
        }),
        child: Box::new(Resource::Memory(MemoryRange::from_pointer_value(
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
    let mut numeric = TermRewrite::for_pointer_exact(source.address(), target.address());
    let rewritten = numeric.proposition(&input);
    let Proposition::ResourceContains { child, .. } = rewritten else {
        panic!("containment")
    };
    let Resource::Memory(range) = child.as_ref() else {
        panic!("memory")
    };
    assert_eq!(range.base(), target.address());
    assert_eq!(range.provenance.as_ref(), source.provenance());
    assert_eq!(range.bounds_owner.as_deref(), source.bounds_owner());
    assert!(!range.carrier_bounds_known);
}

#[test]
fn a_full_pointer_rewrite_does_not_adopt_another_read_carrier_at_the_same_address() {
    let _session = crate::kernel::VerificationSession::enter();
    let retained_state = intern_memory(SymbolicMemory::new());
    let raw = Address::symbolic(Variable(424_110));
    let source = Pointer::from_read(
        raw.clone(),
        ProgramType::Int32Pointer,
        &retained_state,
        &Address::symbolic(Variable(424_111)),
    );
    let unrelated = Pointer::from_read(
        raw,
        ProgramType::Int32Pointer,
        &retained_state,
        &Address::symbolic(Variable(424_112)),
    );
    let target = Pointer::new(
        Address {
            base: AddressBase::Heap(424_113),
            offset: AddressOffset::Constant(0),
        },
        ProgramType::Int32Pointer,
    );
    let input = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(MemoryRange::from_pointer_value(
            &unrelated,
            0u32.into(),
            1u32.into(),
            4,
        ))),
        right: Box::new(Resource::Memory(MemoryRange::new(
            Address::symbolic(Variable(424_114)),
            0u32.into(),
            1u32.into(),
        ))),
    };
    let mut rewrite = TermRewrite::for_pointer_value_exact(&source, &target);
    let Proposition::ResourceSeparate { left, .. } = rewrite.proposition(&input) else {
        panic!("separation")
    };
    let Resource::Memory(range) = left.as_ref() else {
        panic!("memory")
    };
    assert_eq!(range.base(), target.address());
    assert_eq!(range.provenance.as_ref(), unrelated.provenance());
    assert_eq!(range.bounds_owner.as_deref(), unrelated.bounds_owner());
    assert!(!range.carrier_bounds_known);
}

#[test]
fn full_program_argument_pointer_rewrite_reaches_a_displaced_copy() {
    let parameter = |id| {
        Pointer::new(
            Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(id)), 1),
            },
            ProgramType::UInt8Pointer,
        )
    };
    let base = parameter(916_201);
    let middle = parameter(916_202);
    let replacement = base.clone().with_address(base.address().offset_by_bytes(2));
    let displaced = middle
        .clone()
        .with_address(middle.address().offset_by_bytes(3));
    let mut rewrite = TermRewrite::for_pointer_value_exact(&middle, &replacement);
    let ProgramValue::Pointer(actual) = rewrite.value(&ProgramValue::Pointer(displaced)) else {
        panic!("pointer rewrite changed type")
    };
    let expected = base.address().offset_by_bytes(5);
    assert_eq!(actual.address().base, expected.base);
    assert_eq!(
        crate::kernel::eval::canonical_offset_term(&actual.address().offset),
        crate::kernel::eval::canonical_offset_term(&expected.offset)
    );
    assert_eq!(actual.provenance(), base.provenance());
    assert_eq!(actual.bounds_owner(), base.bounds_owner());

    let mut numeric = TermRewrite::for_pointer_exact(middle.address(), replacement.address());
    let ProgramValue::Pointer(address_only) = numeric.value(&ProgramValue::Pointer(middle.clone()))
    else {
        panic!("address rewrite changed type")
    };
    assert_eq!(address_only.provenance(), middle.provenance());
    assert_eq!(address_only.bounds_owner(), middle.bounds_owner());
}

#[test]
fn displaced_symbolic_pointer_rewrite_keeps_selected_bounds() {
    let source = Pointer::new(
        Address::symbolic(Variable(916_211)),
        ProgramType::UInt8Pointer,
    );
    let target_address = Address::symbolic(Variable(916_212));
    let target = Pointer::new(target_address.clone(), ProgramType::UInt8Pointer).with_bounds(Some(
        SubobjectBounds {
            start: target_address.clone(),
            width: 4u32.into(),
        },
    ));
    let shifted = source
        .clone()
        .with_address(source.address().offset_by_bytes(1));
    let ProgramValue::Pointer(actual) = TermRewrite::for_pointer_value_exact(&source, &target)
        .value(&ProgramValue::Pointer(shifted))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.address(), &target_address.offset_by_bytes(1));
    assert_eq!(actual.provenance(), target.provenance());
    assert_eq!(actual.bounds_owner(), target.bounds_owner());
    assert_eq!(actual.bounds(), target.bounds());

    let selected = source
        .clone()
        .with_bounds(Some(SubobjectBounds {
            start: source.address().offset_by_bytes(1),
            width: 1u32.into(),
        }))
        .with_address(source.address().offset_by_bytes(1));
    let ProgramValue::Pointer(narrowed) = TermRewrite::for_pointer_value_exact(&source, &target)
        .value(&ProgramValue::Pointer(selected))
    else {
        panic!("selected pointer type")
    };
    assert_eq!(
        narrowed.bounds(),
        Some(&SubobjectBounds {
            start: target_address.offset_by_bytes(1),
            width: 1u32.into(),
        })
    );

    let ProgramValue::Pointer(numeric) =
        TermRewrite::for_pointer_exact(source.address(), target.address())
            .value(&ProgramValue::Pointer(source.clone()))
    else {
        panic!("numeric pointer type")
    };
    assert_eq!(numeric.provenance(), source.provenance());
    assert_eq!(numeric.bounds_owner(), source.bounds_owner());
    assert_eq!(numeric.bounds(), source.bounds());
}

#[test]
fn displaced_program_argument_rewrite_inherits_known_replacement_bounds() {
    let parameter = |id| {
        Pointer::new(
            Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(id)), 1),
            },
            ProgramType::UInt8Pointer,
        )
    };
    let source = parameter(916_241);
    let base = parameter(916_242);
    let target = base.clone().with_bounds(Some(SubobjectBounds {
        start: base.address().clone(),
        width: 4u32.into(),
    }));
    let input = source
        .clone()
        .with_address(source.address().offset_by_bytes(1));
    let ProgramValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&ProgramValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.bounds(), target.bounds());
    assert_eq!(actual.bounds_are_known(), target.bounds_are_known());
    assert_eq!(actual.bounds_owner(), target.bounds_owner());
}

#[test]
fn displaced_original_pointer_keeps_its_bounds_beside_a_view_equality() {
    let original = Pointer::new(
        Address::symbolic(Variable(916_251)),
        ProgramType::UInt8Pointer,
    );
    let other = Pointer::new(
        Address::symbolic(Variable(916_252)),
        ProgramType::UInt8Pointer,
    );
    let source_view = original
        .clone()
        .with_type(ProgramType::VoidPointer)
        .with_bounds_owner(None);
    let target_view = other
        .clone()
        .with_type(ProgramType::VoidPointer)
        .with_bounds_owner(None);
    let input = original
        .clone()
        .with_address(original.address().offset_by_bytes(3));
    let ProgramValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source_view, &target_view)
            .value(&ProgramValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.address(), &other.address().offset_by_bytes(3));
    assert_eq!(actual.program_type(), original.program_type());
    assert_eq!(actual.bounds_owner(), original.bounds_owner());
    assert_eq!(actual.bounds(), original.bounds());
}

#[test]
fn displaced_copy_keeps_a_domain_not_named_by_the_full_equality() {
    let numeric = Address::symbolic(Variable(916_261));
    let original = Pointer::new(numeric.clone(), ProgramType::UInt8Pointer).with_bounds(Some(
        SubobjectBounds {
            start: numeric.clone(),
            width: 4u32.into(),
        },
    ));
    let memory = intern_memory(SymbolicMemory::new());
    let source = Pointer::from_read(
        numeric.clone(),
        ProgramType::UInt8Pointer,
        &memory,
        &Address::symbolic(Variable(916_263)),
    );
    let target = Pointer::new(
        Address::symbolic(Variable(916_262)),
        ProgramType::UInt8Pointer,
    );
    let input = original.clone().with_address(numeric.offset_by_bytes(1));
    let ProgramValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&source, &target).value(&ProgramValue::Pointer(input))
    else {
        panic!("pointer type")
    };
    assert_eq!(actual.address(), &target.address().offset_by_bytes(1));
    assert_eq!(actual.provenance(), original.provenance());
    assert_eq!(actual.bounds_owner(), original.bounds_owner());
    assert_eq!(
        actual.bounds(),
        Some(&SubobjectBounds {
            start: target.address().clone(),
            width: 4u32.into(),
        })
    );
}

#[test]
fn rewriting_integer_address_zero_keeps_canonical_null_and_displacement() {
    let word = MachineTerm::Variable(Variable(911));
    let bits = MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(!3));
    for value in [0, 1, 2, 3, 4, 5, u64::MAX] {
        for displacement in [0, 8] {
            let mut input = Address::from_integer_address(bits.clone());
            input.offset = AddressOffset::Constant(displacement);
            let replacement = MachineTerm::uint64_constant(value);
            let mut rewrite = TermRewrite::for_bits(&word, &replacement);
            let output = rewrite.pointer(&input);
            assert_eq!(rewrite.refusal(), None);
            assert_eq!(output.offset, input.offset);
            if value < 4 {
                assert_eq!(output.base, Address::null().base);
            } else {
                assert_ne!(output.base, Address::null().base);
                let AddressBase::PureFunctionApplication(application) = output.base else {
                    panic!("a nonzero integer must retain its opaque address")
                };
                assert_eq!(
                    application
                        .integer_address_bits()
                        .unwrap()
                        .uint64_as_const(),
                    Some(value & !3)
                );
            }
        }
    }
}
