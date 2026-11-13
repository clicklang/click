use super::*;
use crate::kernel::VerificationSession;

const PAIRS: [(MachineIntegerType, MachineIntegerType); 4] = [
    (MachineIntegerType::Int8, MachineIntegerType::UInt8),
    (MachineIntegerType::Int16, MachineIntegerType::UInt16),
    (MachineIntegerType::Int32, MachineIntegerType::UInt32),
    (MachineIntegerType::Int64, MachineIntegerType::UInt64),
];

pub(super) fn check_native_parity(root: KernelTerm, destination: MachineIntegerType) {
    // Compare explicit tree exports, independently of native handoffs that
    // retain shared numeric call arguments.
    let export = |root: &KernelTerm| {
        let PureFunctionArgument::Value(value) =
            KernelTermExport::default().argument(root).unwrap()
        else {
            panic!("machine result")
        };
        value
    };
    let native = export(&root);
    let expected =
        crate::kernel::machine_integer::conversion::convert_value(native, destination).unwrap();
    for count in [1, 3] {
        let exports = KernelTermExport::machine_export_count();
        let (path, _) = super::identity_cast_tests::cast_chain(&root, destination.c_type(), count);
        assert!(matches!(path.value, SpecValue::Shared(_)));
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let SpecValue::Shared(root) = path.value else {
            unreachable!()
        };
        assert_eq!(export(&root), expected);
    }
}

#[test]
fn retained_signedness_casts_match_native_terms_and_boundary_constants() {
    let _session = VerificationSession::enter();
    for (signed, unsigned) in PAIRS {
        for (source, destination) in [(signed, unsigned), (unsigned, signed)] {
            let width = source.format().bits();
            let high = num_bigint::BigInt::from(1u8)
                << (width - u32::from(source.format().is_signed())) as usize;
            let mut leaves = vec![
                MachineTerm::Variable(Variable(995420)),
                MachineTerm::opaque_conversion(
                    "cast_boundary",
                    MachineTerm::Variable(Variable(995421)),
                ),
            ];
            for value in [
                num_bigint::BigInt::from(0),
                &high - 1u8,
                if source.format().is_signed() {
                    -high
                } else {
                    1u8.into()
                },
            ] {
                leaves.push(
                    crate::kernel::machine_integer::range::constant_word(source, &value).unwrap(),
                );
            }
            for leaf in leaves {
                let root = KernelTerm::retained_native_machine_operand(source, &leaf);
                check_native_parity(root.clone(), destination);
                let intermediate =
                    shared_machine::cast_signedness(&SpecValue::Shared(root), destination.c_type())
                        .unwrap();
                check_native_parity(intermediate, source);
            }
        }
    }
}

#[test]
fn signed_64_conversion_preserves_existing_extension_spellings() {
    let _session = VerificationSession::enter();
    let variable = MachineTerm::Variable(Variable(995422));
    for native in [
        MachineTerm::uint64_from_32(variable.clone()),
        MachineTerm::uint64_from_int32(variable.clone()),
        MachineTerm::uint64_from_int64(variable),
    ] {
        let root = KernelTermImport::default().machine(MachineIntegerType::UInt64, &native);
        check_native_parity(root, MachineIntegerType::Int64);
    }
}

#[test]
fn signedness_producer_leaves_other_cast_boundaries_unchanged() {
    let _session = VerificationSession::enter();
    let native = SpecValue::Native(CValue::Int32(MachineTerm::Variable(Variable(995423))));
    assert!(shared_machine::cast_signedness(&native, CType::UInt32).is_none());
    let general_call = SpecValue::Shared(KernelTermImport::default().machine(
        MachineIntegerType::Int32,
        &MachineTerm::opaque_conversion("unmigrated_call", MachineTerm::Variable(Variable(995426))),
    ));
    assert!(shared_machine::cast_signedness(&general_call, CType::UInt32).is_none());
    let root = KernelTermImport::default().machine(
        MachineIntegerType::Int32,
        &MachineTerm::Variable(Variable(995423)),
    );
    let value = SpecValue::Shared(root);
    for target in [
        CType::Int32,
        CType::UInt8,
        CType::Int64,
        CType::UInt128,
        CType::Bool,
    ] {
        assert!(shared_machine::cast_signedness(&value, target).is_none());
    }
    let wide = SpecValue::Shared(KernelTermImport::default().machine(
        MachineIntegerType::Int128,
        &MachineTerm::Variable(Variable(995424)),
    ));
    assert!(shared_machine::cast_signedness(&wide, CType::UInt128).is_none());
}

mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/signedness_cast_tests.rs");
}

#[test]
fn cast_variable_guards_keep_native_spelling_without_exporting_arithmetic() {
    use crate::kernel::machine_integer::comparison::condition_for_operand_views;
    use crate::kernel::{CompareRelation, MachineOperandView as V};
    let _session = VerificationSession::enter();
    for (source, destination) in [PAIRS[2], (PAIRS[2].1, PAIRS[2].0)] {
        let variable = MachineTerm::Variable(Variable(995427));
        let root = KernelTermImport::default().machine(source, &variable);
        let cast = shared_machine::cast_signedness(&SpecValue::Shared(root), destination.c_type())
            .unwrap();
        let zero =
            crate::kernel::machine_integer::range::constant_word(destination, &0.into()).unwrap();
        let native =
            crate::kernel::machine_integer::conversion::convert_term(source, destination, variable);
        for relation in [CompareRelation::LessThan, CompareRelation::LessEqual] {
            let exports = KernelTermExport::machine_export_count();
            let actual = condition_for_operand_views(
                destination,
                relation,
                [V::Legacy(&zero), V::Shared(&cast)],
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(
                actual,
                ConditionTerm::machine_compare(destination, relation, zero.clone(), native.clone())
            );
        }
    }
}
