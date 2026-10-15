use super::*;
use crate::kernel::{CMemorySegment, c_uint64_literal};
// Containment keys keep the domain, interface liveness stays wide, and
// changed-cell framing dispatches to the native access rule.
#[test]
fn wide_interface_and_memory_effect_readers_preserve_the_range_kind() {
    let base = Pointer::symbolic(Variable(984_600));
    let wide = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(0),
        Bitvector32Term::UInt64Constant(1 << 33),
        4,
    );
    let resource = CResourceFact::own_memory(wide.clone());
    let segment = CMemorySegment::new(
        CExpression::Value(CValue::pointer(base.clone())),
        c_uint64_literal(0),
        c_uint64_literal(1 << 33),
    );
    let spec = CResourceSpec::owned_memory(segment);
    let before = CMemory::new().with_block(base.block.clone(), 4);
    let state = CState::new().with_memory(before.clone());
    assert!(matches!(
        interface_resource_intrinsic_fact(&spec, &resource, &state),
        Some(Proposition::CMemoryLoadable { wide: true, .. })
    ));
    let after = before.clone().store(base, CValue::Int32(7u32.into()));
    assert!(memory_diff_is_covered_by_ranges(
        &before,
        &after,
        &[wide],
        &PureFactContext::new()
    ));
}
