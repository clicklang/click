use super::*;

#[test]
fn opaque_extent_equality_retains_the_full_value_and_coverage() {
    let base = Pointer::symbolic(Variable(998_801));
    let extent = SubobjectExtent::opaque(Variable(SubobjectExtent::OPAQUE_VARIABLE_BASE + 81));
    let opaque =
        CPointerValue::new(base.clone(), CType::Int32Pointer).with_extent(Some(extent.clone()));
    let known = CPointerValue::new(base.clone(), CType::Int32Pointer)
        .with_extent(Some(SubobjectExtent::constant(base.clone(), 4)));
    let equality = c_value_comparison_proposition(
        &CValue::Pointer(opaque.clone()),
        CComparisonOperator::Equal,
        &CValue::Pointer(known.clone()),
    )
    .unwrap();
    let context = PureFactContext::new().assume_proposition(equality);
    assert!(!context.is_inconsistent());
    assert!(context.pointer_designations_match(&opaque, &known));
    assert!(context.opaque_extent_covers(&extent, &base, 4));
    assert!(!context.opaque_extent_covers(&extent, &base.offset_by_bytes(4), 4));
    let coverage = PureFactContext::new().assume_proposition(extent.coverage_fact(
        &CMemoryRange::new_with_element_width(base, 0u32.into(), 4u32.into(), 1),
    ));
    assert!(!coverage.pointer_designations_match(&opaque, &known));
}

#[test]
fn typed_ranges_keep_opaque_claims_and_root_widening_drops_them() {
    let base = Pointer::symbolic(Variable(998_802));
    let variable = Variable(SubobjectExtent::OPAQUE_VARIABLE_BASE + 82);
    let pointer = CPointerValue::new(base.clone(), CType::Int32Pointer)
        .with_extent(Some(SubobjectExtent::opaque(variable)))
        .with_member_extent(SubobjectExtent::constant(base.clone(), 4));
    let range = CMemoryRange::from_pointer_value(&pointer, 0u32.into(), 1u32.into(), 4);
    assert_eq!(range.designations(), [None, Some(variable)]);
    let copied = range.with_bounds(base.clone(), 0u32.into(), 1u32.into());
    assert_eq!(copied.designations(), range.designations());
    let root = pointer.with_root_extent();
    assert_eq!(root.designations(), [None, None]);
}
