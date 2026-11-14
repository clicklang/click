//! Syntax atoms for equality-premise selection. Registry-derived address atoms
//! are collected by the caller, after this syntax-only cache has been released.
use super::*;

thread_local! {
    static ATOMS: std::cell::RefCell<HashMap<u64, PersistentSet<BitvectorEqualityAtomKey>>> = Default::default();
}

pub(in crate::kernel) fn clear_selected_atom_cache() {
    ATOMS.with(|cache| cache.borrow_mut().clear());
}

fn syntax_atoms(root: &KernelTerm) -> Option<PersistentSet<BitvectorEqualityAtomKey>> {
    ATOMS.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![(root, false)];
        while let Some((term, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            if cache.contains_key(&term.id()) {
                continue;
            }
            let atoms = match term.node() {
                KernelTermNode::Variable(variable) => PersistentSet::default()
                    .with_value(BitvectorEqualityAtomKey::Variable(*variable)),
                KernelTermNode::MachineLiteral(literal) => {
                    let mut atoms = PersistentSet::default();
                    if let Some(atom) = bitvector_equality_atom_key(&literal.legacy_term()) {
                        atoms = atoms.with_value(atom);
                    }
                    atoms
                }
                KernelTermNode::MemoryLoad { .. } => PersistentSet::default().with_value(
                    bitvector_equality_atom_key(term.machine_read_leaf().expect("read leaf"))
                        .expect("read atom"),
                ),
                // Native conversions are opaque. Fold children are collected
                // below with one query-local seen set.
                KernelTermNode::IntegerToMachine { .. }
                | KernelTermNode::Legacy(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::Fold(_)
                | KernelTermNode::Match(_) => PersistentSet::default(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => {
                    if !finish {
                        pending.push((term, true));
                        pending.push((operand, false));
                        continue;
                    }
                    cache[&operand.id()].clone()
                }
                KernelTermNode::MachineBinary {
                    arguments: [left, right],
                    ..
                }
                | KernelTermNode::MachineIf {
                    arguments: [_, left, right],
                } => {
                    if !finish {
                        pending.push((term, true));
                        pending.push((right, false));
                        pending.push((left, false));
                        continue;
                    }
                    let (left, right) = (&cache[&left.id()], &cache[&right.id()]);
                    let (large, small) = if left.len() >= right.len() {
                        (left, right)
                    } else {
                        (right, left)
                    };
                    let mut atoms = large.clone();
                    if !large.shares_root_with(small) {
                        for atom in small.iter() {
                            if crate::instrumentation::deadline_exceeded_with_work(1) {
                                return None;
                            }
                            atoms = atoms.with_value(atom.clone());
                        }
                    }
                    atoms
                }
                _ => unreachable!("shared machine observation fragment"),
            };
            cache.insert(term.id(), atoms);
        }
        Some(cache[&root.id()].clone())
    })
}

pub(super) fn collect(
    machine: &SharedMachineIntegerTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    collect_in(machine, atoms, &mut BTreeSet::new(), false, false);
}

fn collect_in(
    machine: &SharedMachineIntegerTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
    seen: &mut BTreeSet<(u64, bool)>,
    inside_fold: bool,
    native_match_body: bool,
) {
    let Some(root) = machine.shared_operand() else {
        collect_bitvector_atoms(machine.value(), atoms);
        return;
    };
    if !seen.insert((root.id(), native_match_body)) {
        return;
    }
    let Some(written) = syntax_atoms(root) else {
        return;
    };
    for atom in written.iter() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return;
        }
        atoms.insert(atom.clone());
        if let BitvectorEqualityAtomKey::Variable(variable) = atom {
            collect_load_address_atoms(*variable, atoms, 0);
        }
    }
    if let Some(leaves) = crate::kernel::shared_machine_conversion_leaves(root, || {
        !crate::instrumentation::deadline_exceeded_with_work(1)
    }) {
        for (_, leaf) in leaves.iter() {
            if native_match_body && let KernelTermNode::MachineIf { arguments } = leaf.node() {
                let guard = crate::kernel::KernelTermExport::condition(&arguments[0])
                    .expect("retained match/fold guard");
                collect_condition_bitvector_atoms(&guard, atoms);
            }
            if let KernelTermNode::Fold(fold) = leaf.node() {
                for child in &fold.arguments {
                    let child = MachineOperandView::Shared(child).retain(MachineIntegerType::Int32);
                    collect_in(&child, atoms, seen, true, native_match_body);
                }
            }
            if let KernelTermNode::Match(matched) = leaf.node() {
                for child in &matched.arguments[1..] {
                    let child = MachineOperandView::Shared(child).retain(machine.ty());
                    collect_in(&child, atoms, seen, true, true);
                }
            }
            if let Some(native) = leaf.machine_conversion_leaf() {
                if inside_fold {
                    // Native folds visited these children before migration.
                    // Preserve their opaque atoms and dependency rules here.
                    collect_bitvector_atoms(native, atoms);
                } else if let MachineTerm::BoolCast { value, .. } = native {
                    // Ordinary common expressions retain their existing
                    // selection policy; migrating folds must not widen it.
                    collect_condition_bitvector_atoms(value, atoms);
                }
            }
        }
    }
    let Some(reads) = crate::kernel::shared_machine_read_leaves(root, || {
        !crate::instrumentation::deadline_exceeded_with_work(1)
    }) else {
        return;
    };
    for (_, read) in reads.iter() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return;
        }
        let (_, address, _) = MachineOperandView::Shared(read)
            .read()
            .expect("selected read");
        collect_pointer_bitvector_atoms(address, atoms);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_match_atom_selection_keeps_native_conditional_guards() {
        let _session = VerificationSession::enter();
        let native = MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(crate::kernel::KernelMatch::test_scrutinee(vec![])),
            arms: vec![crate::kernel::AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                bindings: vec![],
                binding_names: Default::default(),
                body: MachineTerm::If {
                    condition: Box::new(ConditionTerm::equal(
                        MachineTerm::Variable(Variable(1005397)),
                        MachineTerm::Variable(Variable(1005398)),
                    )),
                    then_term: Box::new(MachineTerm::constant(1)),
                    else_term: Box::new(MachineTerm::constant(0)),
                },
            }],
        };
        let mut expected = BTreeSet::new();
        collect_bitvector_atoms(&native, &mut expected);
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let common =
            SharedMachineIntegerTerm::observe_shared(MachineIntegerType::Int32, root).unwrap();
        let mut actual = BTreeSet::new();
        collect(&common, &mut actual);
        assert_eq!(actual, expected);
        assert!(actual.contains(&BitvectorEqualityAtomKey::Variable(Variable(1005397))));
    }

    #[test]
    fn shared_fold_atom_selection_keeps_call_bodies_opaque() {
        use crate::kernel::{KernelTermExport, KernelTermImport};
        let _session = VerificationSession::enter();
        let native = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(0)),
            end: Box::new(MachineTerm::Variable(Variable(1005390))),
            initial: Box::new(MachineTerm::constant(0)),
            accumulator: Variable(1005391),
            item: Variable(1005392),
            body: Box::new(MachineTerm::ClickFunctionApplication {
                name: "opaque_body".into(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(1005393)),
                ))],
            }),
        };
        let mut expected = BTreeSet::new();
        collect_bitvector_atoms(&native, &mut expected);
        let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let value = SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap();
        let before = KernelTermExport::machine_export_count();
        let mut actual = BTreeSet::new();
        collect(&value, &mut actual);
        assert_eq!(actual, expected);
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn ordinary_shared_atom_selection_does_not_adopt_fold_leaf_rules() {
        let _session = VerificationSession::enter();
        let call = MachineTerm::ClickFunctionApplication {
            name: "ordinary_opaque_call".into(),
            arguments: vec![PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::Variable(Variable(1005394)),
            ))],
        };
        let call_atom = bitvector_equality_atom_key(&call).expect("opaque call atom");
        let native = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(call),
            right: Box::new(MachineTerm::constant(1)),
        };
        let machine = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, native);
        assert!(machine.shared_operand().is_some());
        let mut atoms = BTreeSet::new();
        collect(&machine, &mut atoms);
        assert!(!atoms.contains(&call_atom));
        assert_eq!(
            atoms,
            BTreeSet::from([BitvectorEqualityAtomKey::Constant(1)])
        );
    }

    #[test]
    fn selected_shared_atoms_preserve_literal_conversion_and_load_rules() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(1005300)),
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(1005301)), 4),
        };
        let memory = intern_c_memory(Memory::new());
        let load = crate::kernel::eval::load_variable_for_cell(&memory, &pointer, LoadKind::Int32);
        let conversion = MachineTerm::IntegerToMachine {
            destination: MachineIntegerType::Int32,
            value: IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::Variable(Variable(1005302)),
            ))
            .into(),
        };
        let native = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(load)),
            right: Box::new(MachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: MachineBinaryOp::Multiply,
                left: Box::new(conversion),
                right: Box::new(MachineTerm::uint32_constant(7)),
            }),
        };
        let machine = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, native.clone());
        assert!(machine.shared_operand().is_some());
        let mut expected = BTreeSet::new();
        collect_bitvector_atoms(&native, &mut expected);
        let exports = KernelTermExport::machine_export_count();
        let mut found = BTreeSet::new();
        collect(&machine, &mut found);
        assert_eq!(found, expected);
        assert!(found.contains(&BitvectorEqualityAtomKey::Variable(Variable(1005301))));
        assert!(found.contains(&BitvectorEqualityAtomKey::Constant(7)));
        assert!(!found.contains(&BitvectorEqualityAtomKey::Variable(Variable(1005302))));
        let wide = SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt64,
            MachineTerm::uint64_add(
                MachineTerm::Variable(Variable(1005303)),
                MachineTerm::uint64_constant(7),
            ),
        );
        let mut wide_atoms = BTreeSet::new();
        collect(&wide, &mut wide_atoms);
        assert_eq!(
            wide_atoms,
            BTreeSet::from([BitvectorEqualityAtomKey::Variable(Variable(1005303))])
        );
        // Structural reads own their addresses independently of the registry.
        crate::kernel::eval::clear_load_variable_registry();
        let mut restored = BTreeSet::new();
        collect(&machine, &mut restored);
        assert_eq!(restored, found);
        assert!(!restored.contains(&BitvectorEqualityAtomKey::Variable(load)));
        assert!(restored.contains(&BitvectorEqualityAtomKey::Variable(Variable(1005301))));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/facts/selected_atoms.rs");
    }
}

/// Root-only atom selection for bounded registered-address inspection.
pub(super) fn root_atom(operand: MachineOperandView<'_>) -> Option<BitvectorEqualityAtomKey> {
    match operand {
        MachineOperandView::Legacy(term) => bitvector_equality_atom_key(term),
        MachineOperandView::Shared(root) => match root.node() {
            KernelTermNode::Variable(variable) => {
                Some(BitvectorEqualityAtomKey::Variable(*variable))
            }
            KernelTermNode::MachineLiteral(literal) => {
                bitvector_equality_atom_key(&literal.legacy_term())
            }
            KernelTermNode::MemoryLoad { .. } => {
                bitvector_equality_atom_key(root.machine_read_leaf().expect("read leaf"))
            }
            _ => None,
        },
    }
}
