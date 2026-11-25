use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Address {
    Address {
        base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: OldAddressOffset::Constant(0),
    }
}
fn argument(pointer: Address) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::typed_pointer(
        pointer,
        ProgramType::Int32Pointer,
    ))
}

#[test]
fn rewriting_an_exact_scalar_read_keeps_its_named_point() {
    let _session = VerificationSession::enter();
    let memory = SymbolicMemory::new();
    let point = ProgramPoint::starting_at(&memory).for_exact_read();
    let other = ProgramPoint::starting_at(&memory).for_exact_read();
    assert_ne!(point.id(), other.id());
    let source = Address::symbolic(Variable(1008322));
    let target = Address::symbolic(Variable(1008323));
    let read = |point: &ProgramPoint, address: &Address| {
        OldMachineTerm::read_named(point.clone(), Box::new(address.clone()), LoadKind::Bits64)
    };
    let original = read(&point, &source);
    let expected = read(&point, &target);
    let source_pointer = OldPointer::new(source.clone(), ProgramType::UInt64Pointer);
    let target_pointer = OldPointer::new(target.clone(), ProgramType::UInt64Pointer);
    for mut rewrite in [
        TermRewrite::for_pointer_exact(&source, &target),
        TermRewrite::for_pointer_value_exact(&source_pointer, &target_pointer),
    ] {
        let rewritten = rewrite.bits(&original);
        assert_eq!(rewritten, expected);
        assert_ne!(rewritten, read(&other, &target));
    }
}

#[test]
fn rewriting_an_exact_scalar_index_keeps_its_named_point() {
    let _session = VerificationSession::enter();
    let point = ProgramPoint::starting_at(&SymbolicMemory::new()).for_exact_read();
    let pointer = Address::symbolic(Variable(1008324));
    let read = |address: Address| {
        OldMachineTerm::read_named(point.clone(), Box::new(address), LoadKind::UInt32)
    };
    let from = OldAddressOffset::Constant(0);
    let to = OldAddressOffset::Constant(4);
    let expected = read(pointer.offset_by_bytes(4));
    assert_eq!(
        TermRewrite::for_pointer_offset_exact(&from, &to).bits(&read(pointer.clone())),
        expected
    );

    let variable = OldMachineTerm::Variable(Variable(1008325));
    let replacement = OldMachineTerm::constant(4);
    let indexed = Address {
        base: pointer.base,
        offset: OldAddressOffset::Int32Scaled {
            value: SharedMachineIntegerTerm::index(MachineIntegerType::Int32, variable.clone()),
            byte_width: 1,
        },
    };
    let new_address = TermRewrite::for_bits_checked(&variable, &replacement).pointer(&indexed);
    assert_ne!(new_address, indexed);
    assert_eq!(
        TermRewrite::for_bits_checked(&variable, &replacement).bits(&read(indexed)),
        read(new_address)
    );
}

#[test]
fn rewriting_a_scalar_store_read_keeps_its_program_point() {
    let _session = VerificationSession::enter();
    let source = SymbolicMemory::local_pointer("stored_word");
    let target = Address::symbolic(Variable(1008326));
    let kind = LoadKind::Int32;
    let state = ExecutionState::new().with_memory(
        SymbolicMemory::new()
            .with_declared_scalar_block(source.base.clone(), 4, ProgramType::Int32)
            .store(source.clone(), int32(8)),
    );
    let version = state
        .program_point()
        .indexed_integer_version(&source, kind)
        .unwrap();
    assert!(version.indexed_stored_value().is_some());
    let original = OldMachineTerm::read_named(version.clone(), Box::new(source.clone()), kind);

    let source_pointer = OldPointer::new(source.clone(), ProgramType::Int32Pointer);
    let target_pointer = OldPointer::new(target.clone(), ProgramType::Int32Pointer);
    for mut rewrite in [
        TermRewrite::for_pointer_exact(&source, &target),
        TermRewrite::for_pointer_value_exact(&source_pointer, &target_pointer),
    ] {
        let rewritten = rewrite.bits(&original);
        let OldMachineTerm::MemoryLoad(point, address, load_kind) = rewritten else {
            panic!("the rewritten term is a read");
        };
        assert_eq!(point.read_version_id(), version.read_version_id());
        assert!(point.is_exact_read());
        assert!(point.indexed_stored_value().is_none());
        assert_eq!(*address, target);
        assert_eq!(load_kind, kind);
    }
}

#[test]
fn rewriting_a_scalar_caller_store_read_keeps_its_program_point() {
    let _session = VerificationSession::enter();
    let source = Address {
        base: AddressBase::ExternalArgument,
        offset: OldAddressOffset::Constant(4),
    };
    let target = source.offset_by_bytes(8);
    let kind = LoadKind::Int32;
    let entry = ExecutionState::new().begin_function_entry_memory();
    let state = entry
        .clone()
        .with_memory(entry.memory().clone().store(source.clone(), int32(8)));
    let version = state
        .program_point()
        .indexed_integer_version(&source, kind)
        .expect("indexed caller store");
    assert!(version.indexed_stored_value().is_some());
    let original = OldMachineTerm::read_named(version.clone(), Box::new(source.clone()), kind);
    let rewritten = TermRewrite::for_pointer_exact(&source, &target).bits(&original);
    let OldMachineTerm::MemoryLoad(point, address, load_kind) = rewritten else {
        panic!("the rewritten term is a read");
    };
    assert_eq!(point.read_version_id(), version.read_version_id());
    assert!(point.is_exact_read());
    assert!(point.indexed_stored_value().is_none());
    assert_eq!(*address, target);
    assert_eq!(load_kind, kind);
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
        offset: OldAddressOffset::Constant(0),
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
    input.offset = OldAddressOffset::Constant(8);
    let replacement = Address {
        base: "target".into(),
        offset: OldAddressOffset::Constant(4),
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
    let input = OldMachineTerm::AlgebraicMatch {
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
            body: OldMachineTerm::ClickFunctionApplication {
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
    let OldMachineTerm::AlgebraicMatch { arms, .. } = rewrite.bits(&input) else {
        panic!("lost match")
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::Program(ProgramValue::Pointer(renamed)) = &arms[0].bindings[0] else {
        panic!("lost binder")
    };
    assert_ne!(renamed.address(), &Address::symbolic(bound));
    let expected = OldMachineTerm::ClickFunctionApplication {
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
            OldMachineTerm::Variable(item),
        ))],
    );
    let observed = OldMachineTerm::ClickFunctionApplication {
        name: "observe".into(),
        arguments: vec![argument(application)],
    };
    let fold = OldMachineTerm::RangeFold {
        start: Box::new(OldMachineTerm::constant(0)),
        end: Box::new(OldMachineTerm::constant(4)),
        initial: Box::new(OldMachineTerm::constant(0)),
        accumulator: Variable(611),
        item,
        body: Box::new(observed.clone()),
    };
    let proposition = Proposition::condition_is(
        OldConditionTerm::Compare {
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
        offset: OldAddressOffset::Constant(0),
    };
    let original = OldPointer::new(source.clone(), ProgramType::Int32Pointer).with_bounds(Some(
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
            OldPointer::new(target.clone(), ProgramType::Int32Pointer)
        );
    }
}

#[test]
fn full_pointer_rewrite_changes_read_storage_without_inventing_its_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = intern_memory(SymbolicMemory::new());
    let p = OldPointer::new(Address::symbolic(Variable(421)), ProgramType::Int32Pointer);
    let q = OldPointer::new(Address::symbolic(Variable(422)), ProgramType::Int32Pointer);
    let other = Address::symbolic(Variable(423));
    let read = OldPointer::from_read(
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
    let read = OldPointer::from_read(
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
    let source = OldPointer::from_read(
        Address::symbolic(Variable(424_101)),
        ProgramType::Int32Pointer,
        &retained_state,
        &storage,
    );
    let target_base = Address {
        base: AddressBase::Heap(424_102),
        offset: OldAddressOffset::Constant(0),
    };
    let target = OldPointer::new(target_base.clone(), ProgramType::Int32Pointer).with_bounds(Some(
        SubobjectBounds {
            start: target_base,
            width: 4u32.into(),
        },
    ));
    let relationship = |value: &OldPointer| Proposition::ResourceContains {
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
    assert_eq!(
        range.carrier_owner().map(|owner| &**owner),
        source.bounds_owner()
    );
    assert!(!range.carrier_known());
}

#[test]
fn a_full_pointer_rewrite_does_not_adopt_another_read_carrier_at_the_same_address() {
    let _session = crate::kernel::VerificationSession::enter();
    let retained_state = intern_memory(SymbolicMemory::new());
    let raw = Address::symbolic(Variable(424_110));
    let source = OldPointer::from_read(
        raw.clone(),
        ProgramType::Int32Pointer,
        &retained_state,
        &Address::symbolic(Variable(424_111)),
    );
    let unrelated = OldPointer::from_read(
        raw,
        ProgramType::Int32Pointer,
        &retained_state,
        &Address::symbolic(Variable(424_112)),
    );
    let target = OldPointer::new(
        Address {
            base: AddressBase::Heap(424_113),
            offset: OldAddressOffset::Constant(0),
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
    assert_eq!(
        range.carrier_owner().map(|owner| &**owner),
        unrelated.bounds_owner()
    );
    assert!(!range.carrier_known());
}

#[test]
fn full_program_argument_pointer_rewrite_reaches_a_displaced_copy() {
    let parameter = |id| {
        OldPointer::new(
            Address {
                base: AddressBase::ExternalArgument,
                offset: OldAddressOffset::scale_int32(OldMachineTerm::Variable(Variable(id)), 1),
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
    let source = OldPointer::new(
        Address::symbolic(Variable(916_211)),
        ProgramType::UInt8Pointer,
    );
    let target_address = Address::symbolic(Variable(916_212));
    let target = OldPointer::new(target_address.clone(), ProgramType::UInt8Pointer).with_bounds(
        Some(SubobjectBounds {
            start: target_address.clone(),
            width: 4u32.into(),
        }),
    );
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
        OldPointer::new(
            Address {
                base: AddressBase::ExternalArgument,
                offset: OldAddressOffset::scale_int32(OldMachineTerm::Variable(Variable(id)), 1),
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
    let original = OldPointer::new(
        Address::symbolic(Variable(916_251)),
        ProgramType::UInt8Pointer,
    );
    let other = OldPointer::new(
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
    let original = OldPointer::new(numeric.clone(), ProgramType::UInt8Pointer).with_bounds(Some(
        SubobjectBounds {
            start: numeric.clone(),
            width: 4u32.into(),
        },
    ));
    let memory = intern_memory(SymbolicMemory::new());
    let source = OldPointer::from_read(
        numeric.clone(),
        ProgramType::UInt8Pointer,
        &memory,
        &Address::symbolic(Variable(916_263)),
    );
    let target = OldPointer::new(
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
    let word = OldMachineTerm::Variable(Variable(911));
    let bits =
        OldMachineTerm::uint64_bitwise_and(word.clone(), OldMachineTerm::uint64_constant(!3));
    for value in [0, 1, 2, 3, 4, 5, u64::MAX] {
        for displacement in [0, 8] {
            let mut input = Address::from_integer_address(bits.clone());
            input.offset = OldAddressOffset::Constant(displacement);
            let replacement = OldMachineTerm::uint64_constant(value);
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

#[test]
fn exact_displacement_replacement_keeps_the_retained_offset() {
    let _session = VerificationSession::enter();
    let index = SharedMachineIntegerTerm::index(
        MachineIntegerType::UInt64,
        OldMachineTerm::Variable(Variable(1008337)),
    );
    let from = OldAddressOffset::Int64Scaled {
        value: index,
        byte_width: 8,
        unsigned: true,
    };
    let to = OldAddressOffset::Add(
        Box::new(from.clone()),
        Box::new(OldAddressOffset::Constant(16)),
    );
    let displacement =
        |left| OldAddressOffset::Add(Box::new(left), Box::new(OldAddressOffset::Constant(40)));
    let input = StoredPointerOffset::from_written(&displacement(from.clone()));
    let expected = StoredPointerOffset::from_written(&displacement(to.clone()));
    let mut rewrite = TermRewrite::for_pointer_offset_exact(&from, &to);
    let output = rewrite.contract_offset(&input);
    assert!(rewrite.changed);
    assert!(!input.has_cached_native_offset());
    assert!(!output.has_cached_native_offset());
    assert_eq!(output, expected);
    assert!(!output.has_cached_native_offset());
}
