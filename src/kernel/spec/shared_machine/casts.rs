//! Producer casts preserve the language conversion table's written term.
use super::*;
use crate::kernel::MachineCastSpelling as E;

pub(in crate::kernel::spec) fn cast(value: &SpecValue, target: CType) -> Option<KernelTerm> {
    cast_signedness(value, target)
        .or_else(|| cast_widening(value, target))
        .or_else(|| cast_narrowing(value, target))
        .or_else(|| cast_wide(value, target))
}

/// Narrowing retains the existing modular truncation and low-word rules.
pub(in crate::kernel::spec) fn cast_narrowing(
    value: &SpecValue,
    target: CType,
) -> Option<KernelTerm> {
    let SpecValue::Shared(root) = value else {
        return None;
    };
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let destination = MachineIntegerType::from_c_type(target)?;
    if source.format().bits() <= destination.format().bits()
        || source.format().bits() > 64
        || !root.is_shared_machine_operand()
    {
        return None;
    }
    Some(cast_root(root, source, destination))
}

/// Widening changes only the selected value's format. Native inputs and
/// operands outside the retained machine fragment keep their existing path.
pub(in crate::kernel::spec) fn cast_widening(
    value: &SpecValue,
    target: CType,
) -> Option<KernelTerm> {
    let SpecValue::Shared(root) = value else {
        return None;
    };
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let destination = MachineIntegerType::from_c_type(target)?;
    if source.format().bits() >= destination.format().bits()
        || destination.format().bits() > 64
        || !root.is_shared_machine_operand()
    {
        return None;
    }
    Some(cast_root(root, source, destination))
}

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
    Some(cast_root(root, source, destination))
}

fn cast_root(
    root: &KernelTerm,
    source: MachineIntegerType,
    destination: MachineIntegerType,
) -> KernelTerm {
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
        return KernelTerm::retained_machine_operand(
            destination,
            crate::kernel::MachineOperandView::Legacy(&converted),
        );
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
    result.with_machine_observation_type(destination)
}

/// The bounded 128-bit profile uses the same modular generic cast as the
/// language conversion table, admitting only its existing typed operands.
fn cast_wide(value: &SpecValue, target: CType) -> Option<KernelTerm> {
    let SpecValue::Shared(root) = value else {
        return None;
    };
    let source = MachineIntegerType::from_c_type(value.c_type())?;
    let destination = MachineIntegerType::from_c_type(target)?;
    if source == destination
        || (source.format().bits() != 128 && destination.format().bits() != 128)
        || !root.is_shared_machine_operand()
        || !MachineOperandView::Shared(root).accepts_cast_operand(source)
    {
        return None;
    }
    if matches!(root.node(), KernelTermNode::Legacy(_)) {
        let converted = crate::kernel::machine_integer::conversion::convert_term(
            source,
            destination,
            root.machine_conversion_leaf()?.clone(),
        );
        return Some(KernelTerm::retained_machine_operand(
            destination,
            MachineOperandView::Legacy(&converted),
        ));
    }
    Some(root.checking_machine_cast_preserving_sign_pairs(source, destination))
}
