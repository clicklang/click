use super::*;

#[test]
fn entry_arguments_use_the_frame_at_the_entry_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let entry = ExecutionState::new().with_memory(Memory::new());
    let frame = ExecutionState::at_state(&entry).with_local("frame_binding", int32(7));
    assert!(entry.program_point_id().is_some());
    assert_eq!(entry.program_point_id(), frame.program_point_id());
    assert!(std::ptr::eq(
        declared_resource_argument_state(&entry, &frame, ResourceStateSource::Entry),
        &frame,
    ));
}

#[test]
fn equal_memory_at_a_later_point_does_not_supply_entry_arguments() {
    let _session = crate::kernel::VerificationSession::enter();
    let entry = ExecutionState::new().with_memory(Memory::new());
    let later = entry.clone().with_memory(entry.memory().clone());
    assert_eq!(entry.memory(), later.memory());
    assert_ne!(entry.program_point_id(), later.program_point_id());
    assert!(std::ptr::eq(
        declared_resource_argument_state(&entry, &later, ResourceStateSource::Entry),
        &entry,
    ));
    for source in [ResourceStateSource::Current, ResourceStateSource::Post] {
        assert!(std::ptr::eq(
            declared_resource_argument_state(&entry, &later, source),
            &later,
        ));
    }
}

#[test]
fn missing_point_ids_do_not_identify_independent_states() {
    let entry = ExecutionState::new();
    let other = ExecutionState::new();
    assert!(entry.program_point_id().is_none());
    assert!(other.program_point_id().is_none());
    assert!(std::ptr::eq(
        declared_resource_argument_state(&entry, &other, ResourceStateSource::Entry),
        &entry,
    ));
    assert!(std::ptr::eq(
        declared_resource_argument_state(&entry, &entry, ResourceStateSource::Entry),
        &entry,
    ));
}
