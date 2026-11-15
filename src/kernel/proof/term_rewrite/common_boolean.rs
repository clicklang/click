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
        } else if let Some(addresses) = leaf.pointer_addresses() {
            for address in addresses {
                collect_common_address_carriers(&address, &mut variables);
            }
        } else if let Some(offsets) = leaf.pointer_offsets() {
            crate::kernel::SharedPointerOffset::visit_pair(&offsets, |node| {
                if !variables.visit() {
                    return;
                }
                match node {
                    crate::kernel::KernelPointerOffset::Variable(variable) => {
                        variables.program_values.insert(*variable);
                        collect_registered_load_carriers(*variable, &mut variables);
                    }
                    node => {
                        if let Some(value) = node.index() {
                            collect_machine_operand_carriers(
                                MachineOperandView::Shared(value),
                                &mut variables,
                            );
                        }
                    }
                }
            });
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
        if let KernelTermNode::PointerEqual { arguments } = leaf.node() {
            return Ok(KernelTerm::pointer_equal_raw([
                rewrite.boolean_address(&arguments[0]).ok_or(())?,
                rewrite.boolean_address(&arguments[1]).ok_or(())?,
            ]));
        }
        if let KernelTermNode::PointerOffsetEqual { arguments } = leaf.node() {
            use crate::kernel::{KernelPointerOffset as O, SharedPointerOffset as S};
            let offsets = S::try_map_pair(arguments, |_, node| {
                // This entry point is pointer-variable substitution only:
                // offsets retain their raw shape; registered loads stay closed.
                let node = match node {
                    O::Int32Scaled { value, byte_width } => O::Int32Scaled {
                        value: rewrite.shared_machine_operand(&value).ok_or(())?, byte_width },
                    O::Int64Scaled { value, byte_width, unsigned } => O::Int64Scaled {
                        value: rewrite.shared_machine_operand(&value).ok_or(())?, byte_width, unsigned },
                    node => node,
                };
                node.into_shared().map_err(|_| ())
            })?;
            return Ok(KernelTerm::pointer_offset_equal_raw(offsets));
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

fn collect_common_address_carriers(
    address: &crate::kernel::SharedPointerAddress,
    variables: &mut CarrierVariables,
) {
    if !variables.visit() {
        return;
    }
    // These entry points substitute variables, not exact pointer terms.
    debug_assert!(variables.pointer_terms.is_none());
    collect_pointer_block_carriers(address.node().block.native_atom(), variables);
    address.node().offset.visit_root_in_order(false, |node| {
        if !variables.visit() {
            return;
        }
        match node {
            crate::kernel::KernelPointerOffset::Variable(variable) => {
                variables.program_values.insert(*variable);
                collect_registered_load_carriers(*variable, variables);
            }
            node => {
                if let Some(value) = node.index() {
                    collect_machine_operand_carriers(MachineOperandView::Shared(value), variables);
                }
            }
        }
    });
}

impl TermRewrite<'_> {
    /// The raw address policy used by pointer-variable Boolean values and by
    /// native pointer-call substitution. The numeric callback owns binder scope;
    /// this outer entry has no fact-driven or registered-load normalization.
    fn boolean_address(
        &mut self,
        source: &crate::kernel::SharedPointerAddress,
    ) -> Option<crate::kernel::SharedPointerAddress> {
        use crate::kernel::{
            KernelPointerOffset as O, SharedPointerAddress as A, SharedPointerBlock,
            SharedPointerOffset as S,
        };
        debug_assert!(!self.resolve_registered_loads && self.conditions.is_none());
        let original = &source.node().offset;
        let offsets = S::try_map_pair(&[original.clone(), original.clone()], |_, node| {
            if self.checked_work_exhausted() {
                return Err(());
            }
            let (value, width, wide) = match node {
                O::Int32Scaled { value, byte_width } => (value, byte_width, None),
                O::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => (value, byte_width, Some(unsigned)),
                node => return node.into_shared().map_err(|_| ()),
            };
            let mapped = self.index_bits(&S::exact_index(&value));
            Ok(O::import(&self.rebuilt_index(mapped, width, wide)))
        })
        .ok()?;
        let offset = offsets[0].clone();
        let block = source.node().block.native_atom();
        let replacement = self.pointer_variable.and_then(|(from, to)| match block {
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable)
                if *variable == from =>
            {
                Some(to.clone())
            }
            PointerBlock::ExternalObject(variable) if *variable == from => {
                Some(to.object_identity())
            }
            _ => None,
        });
        let result = if let Some(replacement) = replacement {
            self.changed = true;
            A::new(
                SharedPointerBlock::import(&replacement.block),
                S::add(O::import(&replacement.offset), offset),
            )
        } else {
            // Only the opaque block atom crosses its existing native rewrite
            // boundary. The original shared displacement is handled above.
            let atom = self.pointer(&Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            });
            A::new(SharedPointerBlock::import(&atom.block), offset)
        };
        self.refusal().is_none().then_some(result)
    }
}

pub(in crate::kernel) fn substitute_application_address_bits(
    source: &crate::kernel::SharedPointerAddress,
    from: Variable,
    to: &MachineTerm,
) -> Option<crate::kernel::SharedPointerAddress> {
    let from = MachineTerm::Variable(from);
    let mut rewrite = TermRewrite::for_bits(&from, to);
    let mut variables = rewrite.new_carrier_variables();
    collect_common_address_carriers(source, &mut variables);
    rewrite.reserve_source_variables(variables);
    rewrite.boolean_address(source)
}

pub(in crate::kernel) fn substitute_application_address_pointer(
    source: &crate::kernel::SharedPointerAddress,
    from: Variable,
    to: &Pointer,
) -> Option<crate::kernel::SharedPointerAddress> {
    let mut rewrite = TermRewrite::for_pointer_variable(from, to);
    let mut variables = rewrite.new_carrier_variables();
    collect_common_address_carriers(source, &mut variables);
    rewrite.reserve_source_variables(variables);
    rewrite.boolean_address(source)
}
