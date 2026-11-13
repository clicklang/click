//! Producer casts preserve the language conversion table's written term.
use super::*;
use crate::kernel::MachineCastSpelling as E;

/// Same-width signedness conversions of an already shared operand. Other
/// conversions and native inputs keep their existing compatibility boundary.
pub(in crate::kernel::spec) fn cast_signedness(
    value: &SpecValue,
    target: CType,
) -> Option<KernelTerm> {
    let SpecValue::Shared(root) = value else {
        return None;
    };
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let destination = MachineIntegerType::from_c_type(target)?;
    if source == destination
        || source.format().bits() != destination.format().bits()
        || source.format().bits() > 64
        || !root.is_shared_machine_operand()
    {
        return None;
    }
    // Only explicit native leaves use the native constructor. Shared prefixes
    // never cross this boundary, including when their leaf is opaque.
    let native = match root.node() {
        KernelTermNode::Legacy(_) => root.machine_conversion_leaf().cloned(),
        KernelTermNode::MachineLiteral(literal) => Some(literal.legacy_term()),
        _ => None,
    };
    if let Some(native) = native {
        let converted =
            crate::kernel::machine_integer::conversion::convert_term(source, destination, native);
        return Some(KernelTerm::retained_machine_operand(
            destination,
            crate::kernel::MachineOperandView::Legacy(&converted),
        ));
    }
    let result = if source.format().bits() < 64 {
        // Producer syntax keeps the native constructor's inverse sign pair;
        // checking is allowed a different numeric reading of that pair.
        root.checking_machine_cast_preserving_sign_pairs(source, destination)
    } else if destination == MachineIntegerType::Int64 {
        // Match int64_from_uint64_bits, including its selected extension roots.
        match root.node() {
            KernelTermNode::MachineCast {
                encoding: E::UInt64FromInt64,
                operand,
                ..
            } => operand.clone(),
            KernelTermNode::MachineCast {
                encoding: E::UInt64From32,
                operand,
                ..
            } => {
                operand.checking_legacy_machine_conversion(MachineIntegerType::UInt32, destination)
            }
            KernelTermNode::MachineCast {
                encoding: E::UInt64FromInt32,
                operand,
                ..
            } => operand.checking_legacy_machine_conversion(MachineIntegerType::Int32, destination),
            _ => root.clone(),
        }
    } else {
        root.checking_legacy_machine_conversion(source, destination)
    };
    Some(result.with_machine_observation_type(destination))
}
