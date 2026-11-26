use super::*;

fn hash_of(value: &impl std::hash::Hash) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// SymbolicMemory state hashes name symbolic loads, so tagging every existing (32-bit)
/// size must not change them: an `Int32` size hashes and prints as its
/// byte term. The kind still separates the two sizes of one term.
#[test]
fn a_32_bit_size_hashes_and_prints_as_its_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let bytes = OldMachineTerm::Variable(Variable(7));
    let narrow = AllocationSize::int32(bytes.clone());
    let wide = AllocationSize::new(bytes.clone(), AllocationSizeKind::UInt64);
    assert_eq!(hash_of(&narrow), hash_of(&bytes));
    assert_eq!(format!("{narrow:?}"), format!("{bytes:?}"));
    assert_ne!(narrow, wide);
    assert_ne!(hash_of(&narrow), hash_of(&wide));
}

/// The `allocation` token, its owned range, and its coverage carry the
/// size's kind, and reading the token back recovers it.
#[test]
fn allocation_tokens_and_ranges_carry_the_allocation_size_kind() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = OldAddress {
        base: AddressBase::Heap(3),
        offset: OldAddressOffset::Constant(0).into(),
    };
    for (size, value_is_wide, range_kind) in [
        (AllocationSize::int32(16), false, RangeIndexKind::Int32),
        (
            AllocationSize::new(
                OldMachineTerm::uint64_constant(16),
                AllocationSizeKind::UInt64,
            ),
            true,
            RangeIndexKind::UInt64,
        ),
    ] {
        let token = ResourceFact::own_heap_allocation(base.clone(), &size);
        let (read_base, read_size) = token.allocation_size().expect("an allocation token");
        assert_eq!(read_base.address(), &base);
        assert_eq!(read_size, size);
        assert_eq!(
            token.allocation().map(|(_, bytes)| bytes),
            Some(size.bytes())
        );
        assert_eq!(
            matches!(size.token_value(), ProgramValue::UInt64(_)),
            value_is_wide
        );
        assert_eq!(size.byte_range(base.clone()).kind(), range_kind);
    }
}

/// A 64-bit size spells its element count at `uint64`: `n` of `n * w`
/// and a divisible constant; a 32-bit size keeps the 32-bit reading, and
/// neither reads the other's format.
#[test]
fn a_64_bit_size_counts_its_elements_at_uint64() {
    let _session = crate::kernel::VerificationSession::enter();
    let n = OldMachineTerm::Variable(Variable(7));
    let wide = |bytes| AllocationSize::new(bytes, AllocationSizeKind::UInt64);
    let product = wide(OldMachineTerm::uint64_multiply(
        n.clone(),
        OldMachineTerm::uint64_constant(4),
    ));
    assert_eq!(product.element_count(4), Some(n.clone()));
    assert_eq!(product.element_count(8), None);
    assert_eq!(product.element_count(1), Some(product.bytes().clone()));
    let constant = wide(OldMachineTerm::uint64_constant(1 << 35));
    assert_eq!(
        constant.element_count(8),
        Some(OldMachineTerm::uint64_constant(1 << 32))
    );
    assert_eq!(
        wide(OldMachineTerm::uint64_constant((1 << 35) + 2)).element_count(4),
        None
    );
    let narrow = AllocationSize::int32(OldMachineTerm::multiply(
        n.clone(),
        OldMachineTerm::constant(4),
    ));
    assert_eq!(narrow.element_count(4), Some(n.clone()));
    assert_eq!(
        AllocationSize::int32(product.bytes().clone()).element_count(4),
        None
    );
}

#[test]
fn allocation_size_rewrite_keeps_the_mappers_exact_call_argument_payload() {
    let _session = crate::kernel::VerificationSession::enter();
    let argument = OldMachineTerm::Variable(Variable(10993631));
    let inner = |argument| OldMachineTerm::ClickFunctionApplication {
        name: "size_payload".into(),
        arguments: vec![argument],
    };
    let before = SharedMachineIntegerTerm::intern(
        MachineIntegerType::UInt32,
        inner(PureFunctionArgument::Value(ProgramValue::UInt32(
            argument.clone(),
        ))),
    );
    let after = SharedMachineIntegerTerm::intern(
        MachineIntegerType::UInt32,
        inner(PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, argument),
        )),
    );
    assert_eq!(
        before, after,
        "the observations have the same numeric identity"
    );
    assert_ne!(
        before.structural_value(),
        after.structural_value(),
        "producer payloads differ"
    );
    let outer = |argument| OldMachineTerm::ClickFunctionApplication {
        name: "size_wrapper".into(),
        arguments: vec![PureFunctionArgument::SharedMachine(argument)],
    };
    let original = outer(before);
    let replacement = outer(after.clone());
    assert_eq!(
        original, replacement,
        "native equality observes the argument ID"
    );
    let mapped = AllocationSize::int32(original).map_bytes(|_| replacement);
    let OldMachineTerm::ClickFunctionApplication { arguments, .. } = mapped.bytes() else {
        panic!("call");
    };
    let PureFunctionArgument::SharedMachine(actual) = &arguments[0] else {
        panic!("retained argument");
    };
    assert_eq!(
        actual.structural_value(),
        after.structural_value(),
        "rewrite must keep the new producer payload"
    );
}
