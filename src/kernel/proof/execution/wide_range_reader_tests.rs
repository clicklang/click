use super::*;
use crate::kernel::MemorySegment;
// Containment keys keep the domain, interface liveness stays wide, and
// changed-cell framing dispatches to the native access rule.
#[test]
fn wide_interface_and_memory_effect_readers_preserve_the_range_kind() {
    let base = Pointer::symbolic(Variable(984_600));
    let wide = MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(1 << 33),
        4,
    );
    let resource = ResourceFact::own_memory(wide.clone());
    let segment = MemorySegment::new(
        ProgramExpression::Value(ProgramValue::pointer(base.clone())),
        crate::kernel::program_expression::uint64_literal(0),
        crate::kernel::program_expression::uint64_literal(1 << 33),
    );
    let spec = ResourceSpec::owned_memory(segment);
    let before = Memory::new().with_block(base.block.clone(), 4);
    let state = ExecutionState::new().with_memory(before.clone());
    assert!(matches!(
        interface_resource_intrinsic_fact(&spec, &resource, &state),
        Some(Proposition::MemoryLoadable { wide: true, .. })
    ));
    let after = before.clone().store(base, ProgramValue::Int32(7u32.into()));
    assert!(memory_diff_is_covered_by_ranges(
        &before,
        &after,
        &[wide],
        &PureFactContext::new()
    ));
}
