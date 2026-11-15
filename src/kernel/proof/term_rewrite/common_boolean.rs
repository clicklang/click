//! Pointer substitution's existing Boolean folding policy over shared roots.
use super::*;
use crate::kernel::BooleanOperandView as B;

pub(in crate::kernel) fn substitute_pointer_boolean_value(
    root: &KernelTerm,
    from: Variable,
    to: &Pointer,
) -> Option<KernelTerm> {
    let mut rewrite = TermRewrite::for_pointer_variable(from, to);
    let mut variables = rewrite.new_carrier_variables();
    B::Shared(root).for_each_dependency_leaf(|leaf| {
        if let Some((_, _, operands)) = leaf.comparison() {
            for operand in operands {
                collect_machine_operand_carriers(operand, &mut variables);
            }
        } else {
            collect_condition_carriers(&leaf.identity_leaf(), &mut variables);
        }
    });
    rewrite.reserve_source_variables(variables);
    let result = root.map_boolean_with_connectives::<()>(|leaf| {
        if let KernelTermNode::BoolCompare { format, relation, arguments } = leaf.node() {
            let left = rewrite.shared_machine_operand(&arguments[0]).ok_or(())?;
            let right = rewrite.shared_machine_operand(&arguments[1]).ok_or(())?;
            let arguments = [left, right];
            // The native rewrite canonicalizes only a 64-bit address/zero
            // equality here. Other comparisons retain their written node.
            if *format == MachineIntegerType::Int64 && *relation == CompareRelation::Equal {
                let views = arguments.each_ref().map(MachineOperandView::Shared);
                if [(views[0], views[1]), (views[1], views[0])].into_iter().any(|(address, zero)| {
                    zero.uint64_constant() == Some(0)
                        && matches!(address, MachineOperandView::Shared(root)
                            if matches!(root.machine_conversion_leaf(), Some(MachineTerm::PointerAddress(..))))
                }) {
                    return Ok(KernelTerm::boolean_comparison(*format, *relation, arguments));
                }
            }
            return Ok(KernelTerm::boolean_comparison_raw(*format, *relation, arguments));
        }
        let native = B::Shared(leaf).identity_leaf();
        let result = rewrite.condition(&native);
        if rewrite.refusal().is_some() { return Err(()); }
        Ok(KernelTermImport::default().condition(&result))
    }, |original, children| {
        let boolean = |value| KernelTermImport::default().condition(&ConditionTerm::Constant(value));
        match original.node() {
            KernelTermNode::BoolEqual { .. } => Ok(
                if B::Shared(&children[0]).syntax_equal(B::Shared(&children[1])) {
                    boolean(true)
                } else { KernelTerm::boolean_equal_raw([children[0].clone(), children[1].clone()]) }
            ),
            KernelTermNode::BoolIf { .. } => {
                let mut guard = children[0].clone();
                if let KernelTermNode::BoolCompare { format, relation, arguments } = guard.node()
                    && (*format == MachineIntegerType::Int32
                        || (*format == MachineIntegerType::UInt32 && *relation == CompareRelation::Equal))
                {
                    guard = KernelTerm::boolean_comparison(*format, *relation, arguments.clone());
                } else if let Some(native) = B::Shared(&guard).native_leaf() {
                    guard = KernelTermImport::default().condition(&folded_machine_condition(native.clone()));
                }
                let yes = B::Shared(&children[1]);
                let no = B::Shared(&children[2]);
                Ok(match B::Shared(&guard).constant() {
                    Some(true) => children[1].clone(),
                    Some(false) => children[2].clone(),
                    None if yes.syntax_equal(no) => children[1].clone(),
                    None if yes.constant() == Some(true) && no.constant() == Some(false) => guard,
                    None => KernelTerm::boolean_if_raw([guard, children[1].clone(), children[2].clone()]),
                })
            }
            _ => unreachable!(),
        }
    }).ok();
    result.filter(|_| rewrite.refusal().is_none())
}
