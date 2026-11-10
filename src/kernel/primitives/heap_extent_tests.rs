use super::*;

fn hash_of(value: &impl std::hash::Hash) -> u64 {
    use std::hash::Hasher;
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// Snapshot hashes name symbolic loads, so tagging every existing (32-bit)
/// extent must not change them: an `Int32` extent hashes and prints as its
/// byte term. The kind still separates the two extents of one term.
#[test]
fn a_32_bit_extent_hashes_and_prints_as_its_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let bytes = MachineTerm::Variable(Variable(7));
    let narrow = HeapExtent::int32(bytes.clone());
    let wide = HeapExtent::new(bytes.clone(), HeapExtentKind::UInt64);
    assert_eq!(hash_of(&narrow), hash_of(&bytes));
    assert_eq!(format!("{narrow:?}"), format!("{bytes:?}"));
    assert_ne!(narrow, wide);
    assert_ne!(hash_of(&narrow), hash_of(&wide));
}

/// The `allocation` token, its owned range, and its coverage carry the
/// extent's kind, and reading the token back recovers it.
#[test]
fn allocation_tokens_and_ranges_carry_the_extent_kind() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::Heap(3),
        offset: PointerOffsetTerm::Constant(0),
    };
    for (extent, value_is_wide, range_kind) in [
        (HeapExtent::int32(16), false, RangeIndexKind::Int32),
        (
            HeapExtent::new(MachineTerm::uint64_constant(16), HeapExtentKind::UInt64),
            true,
            RangeIndexKind::UInt64,
        ),
    ] {
        let token = CResourceFact::own_heap_allocation(base.clone(), &extent);
        let (read_base, read_extent) = token.allocation_extent().expect("an allocation token");
        assert_eq!(read_base.pointer(), &base);
        assert_eq!(read_extent, extent);
        assert_eq!(
            token.allocation().map(|(_, bytes)| bytes),
            Some(extent.bytes())
        );
        assert_eq!(
            matches!(extent.token_value(), CValue::UInt64(_)),
            value_is_wide
        );
        assert_eq!(extent.byte_range(base.clone()).kind(), range_kind);
    }
}
