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
                // The native collector treats conversions as opaque too.
                KernelTermNode::IntegerToMachine { .. } | KernelTermNode::Legacy(_) => {
                    PersistentSet::default()
                }
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
    let Some(root) = machine.shared_operand() else {
        collect_bitvector_atoms(machine.value(), atoms);
        return;
    };
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
    fn selected_shared_atoms_preserve_literal_conversion_and_load_rules() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(1005300)),
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(1005301)), 4),
        };
        let memory = intern_c_memory(CMemory::new());
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
