//! Context-local, shared keys for the contradiction index's additive readings.
//! Repeated children contribute a coefficient; they are never expanded as trees.
use super::checked_scalar_facts::ScalarOperandKey as Key;
use super::*;
use crate::kernel::{KernelTerm, KernelTermImport, MachineBinaryOp, MachineOperandView as V};
use crate::persistent::PersistentMap;
use std::sync::Arc;

#[derive(Clone, Debug, Default)]
struct Sum {
    constant: u32,
    atoms: PersistentMap<u64, (KernelTerm, u32)>,
    tree: Option<Arc<SumTree>>,
}
// A compressed binary trie has an insertion-order-independent shape. Its
// rendered term is the canonical sum key; updates rebuild at most 64 shallow
// nodes, rather than sorting/rebuilding every previous addend per statement.
#[derive(Clone, Debug)]
struct SumTree {
    anchor: u64,
    branch: Option<(u32, Arc<SumTree>, Arc<SumTree>)>,
    rendered: KernelTerm,
}
fn join(format: MachineIntegerType, bit: u32, a: Arc<SumTree>, b: Arc<SumTree>) -> Arc<SumTree> {
    let (left, right) = if a.anchor & (1u64 << bit) == 0 {
        (a, b)
    } else {
        (b, a)
    };
    Arc::new(SumTree {
        anchor: left.anchor,
        rendered: KernelTerm::machine_binary_shared_as(
            MachineIntegerType::Int32,
            format,
            MachineBinaryOp::Add,
            [left.rendered.clone(), right.rendered.clone()],
        ),
        branch: Some((bit, left, right)),
    })
}
fn update(
    format: MachineIntegerType,
    tree: Option<&Arc<SumTree>>,
    atom: &KernelTerm,
    coefficient: u32,
) -> Option<Arc<SumTree>> {
    crate::instrumentation::record_deterministic_work(1);
    let leaf = || {
        let rendered = if coefficient == 1 {
            atom.clone()
        } else {
            let value = KernelTermImport::default().machine(
                MachineIntegerType::Int32,
                &Bitvector32Term::constant_at32(format, coefficient),
            );
            KernelTerm::machine_binary_shared_as(
                MachineIntegerType::Int32,
                format,
                MachineBinaryOp::Multiply,
                [atom.clone(), value],
            )
        };
        Arc::new(SumTree {
            anchor: atom.id(),
            branch: None,
            rendered,
        })
    };
    let Some(tree) = tree else {
        return (coefficient != 0).then(leaf);
    };
    let difference = tree.anchor ^ atom.id();
    let separating = (difference != 0).then(|| 63 - difference.leading_zeros());
    if let Some(bit) = separating
        && tree
            .branch
            .as_ref()
            .is_none_or(|(root_bit, _, _)| bit > *root_bit)
    {
        return Some(if coefficient == 0 {
            tree.clone()
        } else {
            join(format, bit, tree.clone(), leaf())
        });
    }
    let Some((bit, left, right)) = &tree.branch else {
        return (coefficient != 0).then(leaf);
    };
    let (changed, kept) = if atom.id() & (1u64 << bit) == 0 {
        (left, right)
    } else {
        (right, left)
    };
    Some(match update(format, Some(changed), atom, coefficient) {
        Some(changed) => join(format, *bit, changed, kept.clone()),
        None => kept.clone(),
    })
}

#[derive(Clone, Debug, Default)]
pub(super) struct EndpointKeys {
    sums: PersistentMap<(u64, MachineIntegerType), Sum>,
    keys: PersistentMap<u64, Key>,
}
impl EndpointKeys {
    pub(super) fn key(&mut self, view: V<'_>) -> Key {
        match view {
            V::Legacy(term) => {
                let canonical = super::proposition_reasoning::order_endpoint_key(term);
                self.normalized_legacy(&canonical)
            }
            V::Shared(term) => self.shared(term),
        }
    }
    pub(super) fn normalized_legacy(&mut self, term: &Bitvector32Term) -> Key {
        self.normalized_legacy_pair(term).1
    }

    pub(super) fn normalized_legacy_pair(&mut self, term: &Bitvector32Term) -> (Key, Key) {
        match KernelTermImport::default().machine_arithmetic(MachineIntegerType::Int32, term) {
            Some(term) => (Key::new(V::Shared(&term)), self.shared(&term)),
            None => {
                let key = Key::Written(term.clone());
                (key.clone(), key)
            }
        }
    }

    fn shared(&mut self, root: &KernelTerm) -> Key {
        if let Some(key) = self.keys.get(&root.id()) {
            return key.clone();
        }
        let view = V::Shared(root);
        let Some((format, MachineBinaryOp::Add, _)) = view
            .binary()
            .filter(|(format, _, _)| format.format().bits() == 32)
        else {
            return Key::new(view);
        };
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, visited)) = pending.pop() {
            if self.sums.contains_key(&(term.id(), format)) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let view = V::Shared(&term);
            let children = view
                .binary()
                .filter(|(found, op, _)| *found == format && *op == MachineBinaryOp::Add);
            let sum = if let Some((_, _, [V::Shared(left), V::Shared(right)])) = children {
                if !visited {
                    pending.push((term.clone(), true));
                    pending.push((right.clone(), false));
                    pending.push((left.clone(), false));
                    continue;
                }
                let left = self.sums.get(&(left.id(), format)).unwrap();
                let right = self.sums.get(&(right.id(), format)).unwrap();
                let (mut left, right) = if left.atoms.len() >= right.atoms.len() {
                    (left.clone(), right)
                } else {
                    (right.clone(), left)
                };
                left.constant = left.constant.wrapping_add(right.constant);
                for (id, (atom, coefficient)) in right.atoms.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    let value = left
                        .atoms
                        .get(id)
                        .map_or(0, |(_, count)| *count)
                        .wrapping_add(*coefficient);
                    left.atoms = if value == 0 {
                        left.atoms.without_key(id)
                    } else {
                        left.atoms.with_inserted(*id, (atom.clone(), value))
                    };
                    left.tree = update(format, left.tree.as_ref(), atom, value);
                }
                left
            } else if let Some(constant) = view.word32_constant() {
                Sum {
                    constant,
                    atoms: PersistentMap::default(),
                    tree: None,
                }
            } else {
                Sum {
                    constant: 0,
                    atoms: PersistentMap::default().with_inserted(term.id(), (term.clone(), 1)),
                    tree: update(format, None, &term, 1),
                }
            };
            self.sums = self.sums.with_inserted((term.id(), format), sum);
        }
        let sum = self.sums.get(&(root.id(), format)).unwrap();
        let rendered = sum.tree.as_ref().map(|tree| tree.rendered.clone());
        let result = if sum.constant != 0 || rendered.is_none() {
            let constant = KernelTermImport::default().machine(
                format,
                &Bitvector32Term::constant_at32(format, sum.constant),
            );
            match rendered {
                Some(root) => KernelTerm::machine_binary_shared_as(
                    MachineIntegerType::Int32,
                    format,
                    MachineBinaryOp::Add,
                    [root, constant],
                ),
                None => constant,
            }
        } else {
            rendered.unwrap()
        };
        let key = Key::new(V::Shared(&result));
        self.keys = self.keys.with_inserted(root.id(), key.clone());
        key
    }
}
