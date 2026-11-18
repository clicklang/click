//! Pointer substitution's existing Boolean folding policy over shared roots.
use super::*;
use crate::kernel::BooleanOperandView as B;

pub(in crate::kernel) fn substitute_pointer_boolean_value(
    root: &KernelTerm,
    from: Variable,
    to: &Address,
) -> Option<KernelTerm> {
    let mut rewrite = TermRewrite::for_pointer_variable(from, to);
    let mut variables = rewrite.new_carrier_variables();
    B::Shared(root).for_each_dependency_leaf(|leaf| {
        if let Some((_, address)) = leaf.read() {
            collect_common_address_carriers(&address, &mut variables);
        } else if let Some((_, operands)) = leaf.machine_arguments() {
            for operand in operands {
                collect_machine_operand_carriers(operand, &mut variables);
            }
        } else if let Some(values) = leaf.pointer_values() {
            for value in values {
                for address in value.addresses() {
                    collect_common_address_carriers(address, &mut variables);
                }
            }
        } else if let Some(addresses) = leaf.pointer_addresses() {
            for address in addresses {
                collect_common_address_carriers(&address, &mut variables);
            }
        } else if let Some(offsets) = leaf.pointer_offsets() {
            crate::kernel::SharedAddressOffset::visit_pair(&offsets, |node| {
                if !variables.visit() {
                    return;
                }
                match node {
                    crate::kernel::KernelAddressOffset::Variable(variable) => {
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
                            if matches!(root.machine_conversion_leaf(), Some(MachineTerm::IntegerAddress(..))))
                }) {
                    return Ok(KernelTerm::boolean_comparison(*format, *relation, arguments));
                }
            }
            return Ok(KernelTerm::boolean_comparison_raw(*format, *relation, arguments));
        }
        if let KernelTermNode::BoolOverflow { format,operation,arguments } = leaf.node() {
            return Ok(KernelTerm::boolean_overflow_raw(*format,*operation,[rewrite.shared_machine_operand(&arguments[0]).ok_or(())?,rewrite.shared_machine_operand(&arguments[1]).ok_or(())?]));
        }
        if let KernelTermNode::BoolRead(read) = leaf.node() {
            let (memory,address) = read.parts();
            return Ok(KernelTerm::boolean_read(memory.clone(),rewrite.boolean_address(address).ok_or(())?));
        }
        if let KernelTermNode::PointerEqual(pair) = leaf.node() {
            let [a,b] = pair.arguments();
            return Ok(KernelTerm::pointer_equal([rewrite.boolean_pointer_value(a).ok_or(())?,rewrite.boolean_pointer_value(b).ok_or(())?]));
        }
        if let KernelTermNode::AddressEqual { arguments } = leaf.node() {
            return Ok(KernelTerm::address_equal_raw([
                rewrite.boolean_address(&arguments[0]).ok_or(())?,
                rewrite.boolean_address(&arguments[1]).ok_or(())?,
            ]));
        }
        if let KernelTermNode::AddressOffsetEqual { arguments } = leaf.node() {
            use crate::kernel::{KernelAddressOffset as O, SharedAddressOffset as S};
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
            return Ok(KernelTerm::address_offset_equal_raw(offsets));
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
    address: &crate::kernel::SharedAddress,
    variables: &mut CarrierVariables,
) {
    if !variables.visit() {
        return;
    }
    // These entry points substitute variables, not exact pointer terms.
    debug_assert!(variables.pointer_terms.is_none());
    collect_address_base_carriers(address.node().base.native_atom(), variables);
    address.node().offset.visit_root_in_order(false, |node| {
        if !variables.visit() {
            return;
        }
        match node {
            crate::kernel::KernelAddressOffset::Variable(variable) => {
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
        source: &crate::kernel::SharedAddress,
    ) -> Option<crate::kernel::SharedAddress> {
        use crate::kernel::{
            KernelAddressOffset as O, SharedAddress as A, SharedAddressBase,
            SharedAddressOffset as S,
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
        let block = source.node().base.native_atom();
        let replacement = self.pointer_variable.and_then(|(from, to)| match block {
            AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable)
                if *variable == from =>
            {
                Some(to.clone())
            }
            AddressBase::ExternalObject(variable) if *variable == from => {
                Some(to.object_identity())
            }
            _ => None,
        });
        let result = if let Some(replacement) = replacement {
            self.changed = true;
            A::new(
                SharedAddressBase::import(&replacement.base),
                S::add(O::import(&replacement.offset), offset),
            )
        } else {
            // Only the opaque block atom crosses its existing native rewrite
            // boundary. The original shared displacement is handled above.
            let atom = self.pointer(&Address {
                base: block.clone(),
                offset: AddressOffset::Constant(0),
            });
            A::new(SharedAddressBase::import(&atom.base), offset)
        };
        self.refusal().is_none().then_some(result)
    }
}

pub(in crate::kernel) fn substitute_application_address_bits(
    source: &crate::kernel::SharedAddress,
    from: Variable,
    to: &MachineTerm,
) -> Option<crate::kernel::SharedAddress> {
    let from = MachineTerm::Variable(from);
    let mut rewrite = TermRewrite::for_bits(&from, to);
    let mut variables = rewrite.new_carrier_variables();
    collect_common_address_carriers(source, &mut variables);
    rewrite.reserve_source_variables(variables);
    rewrite.boolean_address(source)
}

pub(in crate::kernel) fn substitute_application_address_pointer(
    source: &crate::kernel::SharedAddress,
    from: Variable,
    to: &Address,
) -> Option<crate::kernel::SharedAddress> {
    let mut rewrite = TermRewrite::for_pointer_variable(from, to);
    let mut variables = rewrite.new_carrier_variables();
    collect_common_address_carriers(source, &mut variables);
    rewrite.reserve_source_variables(variables);
    rewrite.boolean_address(source)
}

impl TermRewrite<'_> {
    /// Complete formal-variable substitution, retaining the native provenance
    /// and opaque-domain policy. This entry has no exact-value or fact rewrite.
    fn boolean_pointer_value(
        &mut self,
        source: &crate::kernel::SharedPointer,
    ) -> Option<crate::kernel::SharedPointer> {
        use crate::kernel::{
            KernelAddressOffset as O, SharedAddress as A, SharedAddressOffset as S,
            SharedPointer as V,
        };
        let (from, to) = self.pointer_variable?;
        debug_assert!(
            self.pointer_value_exact.is_none()
                && self.typed_variables.is_none()
                && !self.pointer_addresses_only
        );
        let p = source.node();
        let base = A::import(&Address {
            base: p.address.node().base.native_atom().clone(),
            offset: AddressOffset::Constant(0),
        });
        let selected = |address: &A| matches!(address.node().base.native_atom(),AddressBase::Symbolic(v)|AddressBase::FunctionSymbolic(v) if *v == from);
        let replacement = (selected(&p.address) && p.provenance.syntax_equal(&base))
            .then(|| V::import(&Pointer::new(to.clone(), p.program_type)));
        let target_identity = A::import(&to.object_identity());
        let provenance = if let Some(target) = &replacement {
            target.node().provenance.clone()
        } else if selected(&p.provenance) {
            target_identity.clone()
        } else {
            self.boolean_address(&p.provenance)?
        };
        let opaque = match &p.bounds_owner {
            None => None,
            Some(origin) if replacement.is_some() && origin.syntax_equal(&base) => {
                replacement.as_ref().unwrap().node().bounds_owner.clone()
            }
            Some(origin) if selected(origin) => Some(target_identity),
            Some(origin) => Some(self.boolean_address(origin)?),
        };
        let mut mapped = source
            .map_condition_addresses(|address| self.boolean_address(address).ok_or(()))
            .ok()?
            .node()
            .clone();
        mapped.provenance = provenance;
        mapped.bounds_owner = opaque;
        if !p.qualifiers.as_ref().is_some_and(|q| q.bounds_known)
            && let Some(replacement) = replacement
        {
            let q = replacement.node().qualifiers.as_ref();
            if q.is_some_and(|q| q.bounds_known) || q.and_then(|q| q.bounds.as_ref()).is_some() {
                let qualifiers = std::sync::Arc::make_mut(
                    mapped.qualifiers.get_or_insert_with(Default::default),
                );
                qualifiers.bounds = q.and_then(|q| q.bounds.clone());
                qualifiers.bounds_known = true;
                mapped.bounds_owner = None;
            }
        }
        // Native condition rewriting canonicalizes addresses after replacing
        // the complete value, without rewriting the retained bounds width.
        V::new(mapped)
            .map_condition_addresses(|address| {
                let offsets = S::try_map_pair(
                    &[address.node().offset.clone(), address.node().offset.clone()],
                    |_, node| {
                        let mapped = match node {
                            O::Add([a, b]) => return Ok::<_, ()>(S::add(a, b)),
                            O::Int32Scaled { value, byte_width } => {
                                let index = S::exact_index(&value);
                                if let Some(written) = index.retained_written_operand() {
                                    return Ok(O::import(&AddressOffset::scale_int32(
                                        crate::kernel::eval::canonical_term(written),
                                        byte_width,
                                    )));
                                }
                                O::Int32Scaled { value, byte_width }
                            }
                            O::Int64Scaled {
                                value,
                                byte_width,
                                unsigned,
                            } => {
                                let index = S::exact_index(&value);
                                if let Some(written) = index.retained_written_operand() {
                                    return Ok(O::import(&AddressOffset::scale_int64(
                                        crate::kernel::eval::canonical_term(written),
                                        byte_width,
                                        unsigned,
                                    )));
                                }
                                O::Int64Scaled {
                                    value,
                                    byte_width,
                                    unsigned,
                                }
                            }
                            node => node,
                        };
                        mapped.into_shared().map_err(|_| ())
                    },
                )?;
                Ok::<_, ()>(A::new(address.node().base.clone(), offsets[0].clone()))
            })
            .ok()
            .filter(|_| self.refusal().is_none())
    }
}
