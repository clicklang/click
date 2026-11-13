use super::signedness_cast_tests::check_native_parity;
use super::*;
use crate::kernel::VerificationSession;

const FORMATS: [MachineIntegerType; 8] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
];

#[test]
fn retained_narrowing_casts_match_native_terms_at_every_supported_width() {
    let _session = VerificationSession::enter();
    for source in FORMATS {
        for destination in FORMATS {
            if source.format().bits() <= destination.format().bits() {
                continue;
            }
            let variable = MachineTerm::Variable(Variable(995440));
            let one =
                crate::kernel::machine_integer::range::constant_word(source, &1.into()).unwrap();
            let high = num_bigint::BigInt::from(1u8)
                << (source.format().bits() - u32::from(source.format().is_signed())) as usize;
            let mut operands = vec![
                variable.clone(),
                MachineTerm::opaque_conversion("narrow_boundary", variable.clone()),
                MachineTerm::Binary {
                    format: source,
                    op: MachineBinaryOp::Add,
                    left: Box::new(variable.clone()),
                    right: Box::new(one),
                },
            ];
            for value in [
                0.into(),
                &high - 1u8,
                if source.format().is_signed() {
                    -high
                } else {
                    1u8.into()
                },
            ] {
                operands.push(
                    crate::kernel::machine_integer::range::constant_word(source, &value).unwrap(),
                );
            }
            // Narrow an existing conversion, including a widening or a sign
            // pair: preserve the native constructor's exact composition rule.
            for original in FORMATS {
                operands.push(crate::kernel::machine_integer::conversion::convert_term(
                    original,
                    source,
                    variable.clone(),
                ));
            }
            for operand in operands {
                let root = KernelTerm::retained_machine_operand(
                    source,
                    MachineOperandView::Legacy(&operand),
                );
                check_native_parity(root, destination);
            }
        }
    }
}

#[test]
fn narrowing_producer_keeps_other_boundaries_outside_its_slice() {
    let _session = VerificationSession::enter();
    let native = SpecValue::Native(CValue::Int32(MachineTerm::Variable(Variable(995441))));
    assert!(shared_machine::cast_narrowing(&native, CType::Int8).is_none());
    let root = KernelTermImport::default().machine(
        MachineIntegerType::Int32,
        &MachineTerm::Variable(Variable(995441)),
    );
    for target in [
        CType::Int64,
        CType::UInt64,
        CType::Int32,
        CType::UInt32,
        CType::Int128,
        CType::Bool,
    ] {
        assert!(shared_machine::cast_narrowing(&SpecValue::Shared(root.clone()), target).is_none());
    }
    let call = KernelTermImport::default().machine(
        MachineIntegerType::Int32,
        &MachineTerm::opaque_conversion(
            "unmigrated_narrow",
            MachineTerm::Variable(Variable(995441)),
        ),
    );
    assert!(shared_machine::cast_narrowing(&SpecValue::Shared(call), CType::Int8).is_none());
}

mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/narrowing_cast_tests.rs");
}
