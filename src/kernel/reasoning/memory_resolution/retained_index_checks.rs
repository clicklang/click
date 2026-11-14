use super::*;
use crate::kernel::{
    KernelTerm, KernelTermExport, KernelType, MachineBinaryOp, MachineIntegerType,
    MachineOperandView, SharedMachineIntegerTerm, VerificationSession,
};

fn retained_index(ty: MachineIntegerType, id: u64) -> SharedMachineIntegerTerm {
    let atom = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(id));
    let zero = KernelTerm::retained_machine_operand(
        ty,
        MachineOperandView::Legacy(&if ty == MachineIntegerType::UInt64 {
            MachineTerm::uint64_constant(0)
        } else {
            MachineTerm::constant(0)
        }),
    );
    let root = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [atom, zero]);
    MachineOperandView::Shared(&root).retain(ty)
}
fn wide(value: SharedMachineIntegerTerm, byte_width: i64) -> PointerOffsetTerm {
    PointerOffsetTerm::Int64Scaled {
        value,
        byte_width,
        unsigned: true,
    }
}
fn equality(
    value: &SharedMachineIntegerTerm,
    ty: MachineIntegerType,
    constant: &MachineTerm,
) -> ConditionTerm {
    crate::kernel::machine_integer::comparison::condition_for_operand_views(
        ty,
        CompareRelation::Equal,
        [value.operand_view(), MachineOperandView::Legacy(constant)],
    )
}

#[test]
fn retained_wide_distinctness_uses_full_words_and_preserves_shape_refusals() {
    let _session = VerificationSession::enter();
    let ty = MachineIntegerType::UInt64;
    let a = retained_index(ty, 994500);
    let b = retained_index(ty, 994501);
    let left = wide(a.clone(), 4);
    let right = wide(b.clone(), 4);
    let root = PureFactContext::new();
    let facts = [
        equality(&a, ty, &MachineTerm::uint64_constant(0)),
        equality(&b, ty, &MachineTerm::uint64_constant(1 << 32)),
    ];
    let context = facts
        .iter()
        .fold(root.clone(), |c, f| c.assume_condition(f.clone(), true));
    let exports = KernelTermExport::machine_export_count();
    assert_eq!(
        wide_element_offsets_proven_distinct(&left, &right, &context),
        Some(true)
    );
    assert_eq!(
        wide_element_offsets_proven_distinct(&left, &right, &root),
        Some(false)
    );
    for (a, b) in [
        (&right, &PointerOffsetTerm::Constant(0)),
        (&PointerOffsetTerm::Constant(0), &right),
    ] {
        assert_eq!(
            wide_element_offsets_proven_distinct(a, b, &context),
            Some(true)
        );
    }
    assert_eq!(
        wide_element_offsets_proven_distinct(&left, &left, &context),
        Some(false)
    );
    assert_eq!(
        wide_element_offsets_proven_distinct(&left, &wide(b.clone(), 8), &context),
        Some(false)
    );
    assert_eq!(
        wide_element_offsets_proven_distinct(&right, &PointerOffsetTerm::Constant(1), &context),
        None
    );
    assert_eq!(
        wide_element_offsets_proven_distinct(&wide(a, 0), &wide(b, 0), &context),
        Some(false)
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn exact_index_constant_substitution_requires_its_selected_fact_and_fitting_product() {
    let _session = VerificationSession::enter();
    let ty = MachineIntegerType::Int32;
    let value = retained_index(ty, 994510);
    let fact = Proposition::ConditionIs(equality(&value, ty, &MachineTerm::constant(7)), true);
    let parent = PureFactContext::new();
    let context = parent.clone().assume_proposition(fact.clone());
    let pointer = |width| Pointer {
        block: "retained-exact-index".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: value.clone(),
            byte_width: width,
        },
    };
    let address = pointer(4);
    let native_source =
        ConditionTerm::equal(value.structural_value().clone(), MachineTerm::constant(7));
    let native_context = parent.clone().assume_condition(native_source, true);
    let false_context = parent.clone().assume_proposition(Proposition::ConditionIs(
        equality(&value, ty, &MachineTerm::constant(7)),
        false,
    ));
    let exports = KernelTermExport::machine_export_count();
    assert_eq!(
        pointer_with_exact_index_constants(&address, &context).offset,
        PointerOffsetTerm::Constant(28)
    );
    assert_eq!(
        pointer_with_exact_index_constants(&address, &parent),
        address
    );
    assert_eq!(
        pointer_with_exact_index_constants(&pointer(i64::MAX), &context),
        pointer(i64::MAX)
    );
    assert_eq!(
        pointer_with_exact_index_constants(&address, &native_context).offset,
        PointerOffsetTerm::Constant(28)
    );
    assert_eq!(
        pointer_with_exact_index_constants(&address, &false_context),
        address
    );
    let seven = MachineTerm::constant(7);
    assert!(
        context.int32_values_known_equal_views(
            value.operand_view(),
            MachineOperandView::Legacy(&seven)
        )
    );
    assert!(
        !parent.int32_values_known_equal_views(
            value.operand_view(),
            MachineOperandView::Legacy(&seven)
        )
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/reasoning/memory_resolution/retained_index_checks.rs");
}
