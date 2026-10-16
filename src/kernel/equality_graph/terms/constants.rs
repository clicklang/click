//! Literal values and selected conditional/load witnesses on shared term roots.
use super::{MachineAtom, TermClasses};
use crate::kernel::assumptions::{SignedConstantResolution, memory_blind_pointer_fingerprint};
use crate::kernel::prelude::*;

#[derive(Clone, Default)]
pub(super) struct ScalarWitnesses {
    conditionals:
        crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<MachineAtom>>,
    loads: crate::persistent::PersistentMap<
        u64,
        crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<MachineAtom>>,
    >,
    settled:
        crate::persistent::PersistentMap<u64, crate::persistent::PersistentMap<MachineAtom, u64>>,
    inverse_bytes: crate::persistent::PersistentMap<u64, crate::persistent::PersistentSet<u64>>,
}

impl TermClasses {
    pub(super) fn register_scalar_witness(&mut self, term: &Bitvector32Term, node: u64) {
        let root = self.root(node);
        let key = MachineAtom::int32(term.clone());
        if matches!(term, Bitvector32Term::If { .. }) {
            let terms = self
                .scalar_witnesses
                .conditionals
                .get(&root)
                .cloned()
                .unwrap_or_default();
            if !terms.contains(&key) {
                self.weights.insert(root, self.weight(root) + 1);
                self.scalar_witnesses
                    .conditionals
                    .insert(root, terms.with_value(key.clone()));
            }
        }
        if let Some((fingerprint, _)) = load_key(term) {
            let mut loads = self
                .scalar_witnesses
                .loads
                .get(&root)
                .cloned()
                .unwrap_or_default();
            let terms = loads.get(&fingerprint).cloned().unwrap_or_default();
            if !terms.contains(&key) {
                self.weights.insert(root, self.weight(root) + 1);
                loads.insert(fingerprint, terms.with_value(key.clone()));
                self.scalar_witnesses.loads.insert(root, loads);
            }
            if self.int32_constants.contains_key(&root) {
                let settled = self
                    .scalar_witnesses
                    .settled
                    .get(&fingerprint)
                    .cloned()
                    .unwrap_or_default();
                self.scalar_witnesses
                    .settled
                    .insert(fingerprint, settled.with_inserted(key, node));
            }
        }
    }

    pub(super) fn register_byte_inverse(&mut self, result: u64, byte: u64) {
        let root = self.root(result);
        let bytes = self
            .scalar_witnesses
            .inverse_bytes
            .get(&root)
            .cloned()
            .unwrap_or_default();
        if !bytes.contains(&byte) {
            self.weights.insert(root, self.weight(root) + 1);
            self.scalar_witnesses
                .inverse_bytes
                .insert(root, bytes.with_value(byte));
        }
        let mut pending = Vec::new();
        self.inverse_byte_values(
            root,
            Some(&crate::persistent::PersistentSet::default().with_value(byte)),
            &mut pending,
        );
        self.close(pending);
    }

    /// The constant of the byte `u` given the constant of `int8(u)`. A known
    /// signed value `k` in `-128..=127` is the conversion of exactly one byte,
    /// `k mod 256`. A value outside that range is the conversion of no byte: the
    /// context is contradictory, and the byte is left as it was rather than given
    /// a value it cannot have. `Unknown` and `Ambiguous` add nothing.
    fn inverse_byte_values(
        &mut self,
        root: u64,
        selected: Option<&crate::persistent::PersistentSet<u64>>,
        pending: &mut Vec<(u64, u64)>,
    ) {
        let Some(value @ -128..=127) = self.int32_constants.get(&root).copied() else {
            return;
        };
        let bytes = selected.cloned().unwrap_or_else(|| {
            self.scalar_witnesses
                .inverse_bytes
                .get(&root)
                .cloned()
                .unwrap_or_default()
        });
        if bytes.is_empty() {
            return;
        }
        let value = self.intern_node(super::Node::Int32(MachineAtom::int32(
            Bitvector32Term::Constant(u32::from(value as i8 as u8)),
        )));
        for byte in bytes.iter() {
            pending.push((*byte, value));
        }
    }

    pub(super) fn merge_scalar_witnesses(
        &mut self,
        moved: u64,
        kept: u64,
        kept_was_settled: bool,
        pending: &mut Vec<(u64, u64)>,
    ) {
        if self.scalar_conflicts.contains(&moved) {
            self.scalar_conflicts = self.scalar_conflicts.without_value(&moved);
            self.mark_scalar_conflict(kept);
            let uses = self.constant_uses.get(&moved).cloned().unwrap_or_default();
            for id in uses.iter() {
                self.mark_scalar_conflict(*id);
            }
        }
        let moved_members = self.scalar_witnesses.conditionals.get(&moved).cloned();
        self.scalar_witnesses.conditionals.remove(&moved);
        if let Some(moved_members) = moved_members {
            let mut members = self
                .scalar_witnesses
                .conditionals
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            for member in moved_members.iter() {
                members = members.with_value(member.clone());
            }
            self.scalar_witnesses.conditionals.insert(kept, members);
        }
        let new_inverse_bytes = self.scalar_witnesses.inverse_bytes.get(&moved).cloned();
        self.scalar_witnesses.inverse_bytes.remove(&moved);
        if let Some(moved_bytes) = &new_inverse_bytes {
            let mut bytes = self
                .scalar_witnesses
                .inverse_bytes
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            for byte in moved_bytes.iter() {
                bytes = bytes.with_value(*byte);
            }
            self.scalar_witnesses.inverse_bytes.insert(kept, bytes);
        }
        let new_loads = self.scalar_witnesses.loads.get(&moved).cloned();
        self.scalar_witnesses.loads.remove(&moved);
        if let Some(moved_loads) = &new_loads {
            let mut loads = self
                .scalar_witnesses
                .loads
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            for (key, members) in moved_loads.iter() {
                let mut bucket = loads.get(key).cloned().unwrap_or_default();
                for member in members.iter() {
                    bucket = bucket.with_value(member.clone());
                }
                loads.insert(*key, bucket);
            }
            self.scalar_witnesses.loads.insert(kept, loads);
        }
        // A class reaches a literal once. Existing settled members retain
        // their immutable node IDs, so later merges need no relabelling scan.
        if self.int32_constants.contains_key(&kept) {
            let newly_settled = if kept_was_settled {
                new_loads
            } else {
                self.scalar_witnesses.loads.get(&kept).cloned()
            };
            if let Some(loads) = newly_settled {
                for (key, members) in loads.iter() {
                    let mut settled = self
                        .scalar_witnesses
                        .settled
                        .get(key)
                        .cloned()
                        .unwrap_or_default();
                    for member in members.iter() {
                        if !settled.contains_key(member) {
                            settled.insert(member.clone(), kept);
                        }
                    }
                    self.scalar_witnesses.settled.insert(*key, settled);
                }
            }
            if !kept_was_settled {
                self.inverse_byte_values(kept, None, pending);
            } else if let Some(bytes) = new_inverse_bytes.as_ref() {
                self.inverse_byte_values(kept, Some(bytes), pending);
            }
        }
    }

    pub(in crate::kernel::equality_graph) fn scalar_constant_of_class(
        &self,
        id: u64,
    ) -> SignedConstantResolution {
        let root = self.root(id);
        if self.scalar_conflicts.contains(&root) {
            return SignedConstantResolution::Ambiguous;
        }
        self.int32_constants
            .get(&root)
            .map_or(SignedConstantResolution::Unknown, |value| {
                SignedConstantResolution::Known(i64::from(*value))
            })
    }
    pub(in crate::kernel::equality_graph) fn scalar_conditional_members(
        &self,
        id: u64,
    ) -> Vec<Bitvector32Term> {
        self.scalar_witnesses
            .conditionals
            .get(&self.root(id))
            .into_iter()
            .flat_map(|members| members.iter())
            .map(|term| term.value().clone())
            .collect()
    }
    pub(in crate::kernel::equality_graph) fn scalar_settled_loads_at(
        &self,
        key: u64,
    ) -> Vec<(Bitvector32Term, u64)> {
        self.scalar_witnesses
            .settled
            .get(&key)
            .into_iter()
            .flat_map(|members| members.iter())
            .map(|(term, node)| (term.value().clone(), self.root(*node)))
            .collect()
    }
    pub(in crate::kernel::equality_graph) fn scalar_bridgeable_loads(
        &self,
        id: u64,
    ) -> Vec<(Bitvector32Term, Bitvector32Term, u64)> {
        let root = self.root(id);
        let mut result = Vec::new();
        if let Some(loads) = self.scalar_witnesses.loads.get(&root) {
            for (key, members) in loads.iter() {
                for (candidate, node) in self.scalar_settled_loads_at(*key) {
                    if node == root {
                        continue;
                    }
                    for member in members.iter() {
                        result.push((member.value().clone(), candidate.clone(), node));
                    }
                }
            }
        }
        result
    }
}

/// The operand of an integer conversion between types that fit a 32-bit
/// word, such as a signed byte read or a C narrowing conversion, with its
/// source and destination. Its constant is a function of the operand's.
pub(super) fn word_cast_operand(
    term: &Bitvector32Term,
) -> Option<(
    &Bitvector32Term,
    crate::kernel::MachineIntegerType,
    crate::kernel::MachineIntegerType,
)> {
    match term {
        Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        } if source.format().bits() <= 32 && destination.format().bits() <= 32 => {
            Some((value, *source, *destination))
        }
        _ => None,
    }
}

/// The byte load a signed byte read converts, when its operand is one.
///
/// Inverting `int8(u) == k` needs `u` in `0..=255`, the domain on which the
/// conversion is injective. A `UInt8` memory load (or the registered
/// variable naming one) holds exactly one byte, zero-extended, whatever
/// produced the term, so its range is structural rather than a fact. Other
/// operands are folded forward but never inverted.
pub(super) fn signed_byte_load_operand(term: &Bitvector32Term) -> Option<&Bitvector32Term> {
    let operand = term.signed_byte_operand()?;
    matches!(
        crate::kernel::eval::viewed_as_memory_load(operand),
        Some(Bitvector32Term::MemoryLoad(
            _,
            _,
            crate::kernel::LoadKind::UInt8
        ))
    )
    .then_some(operand)
}

/// Folds an arithmetic term from its operands' resolutions: `Ambiguous` if
/// any operand is, the evaluated constant if every operand is known, and
/// `Unknown` otherwise (including a term that is not arithmetic).
pub(in crate::kernel) fn fold_arithmetic(
    term: &Bitvector32Term,
    mut operand: impl FnMut(&Bitvector32Term) -> SignedConstantResolution,
) -> SignedConstantResolution {
    // Literal operands need no contextual class query or recursion guard.
    let mut operand = |term: &Bitvector32Term| {
        signed_bitvector_constant(term)
            .map(SignedConstantResolution::Known)
            .unwrap_or_else(|| operand(term))
    };
    if let Some((operator, left, right)) = term.as_binary()
        && operator.is_bitvector32()
    {
        return match (operand(left), operand(right)) {
            (SignedConstantResolution::Ambiguous, _) | (_, SignedConstantResolution::Ambiguous) => {
                SignedConstantResolution::Ambiguous
            }
            (SignedConstantResolution::Known(left), SignedConstantResolution::Known(right)) => {
                SignedConstantResolution::from_term(operator.build(
                    Bitvector32Term::Constant(left as i32 as u32),
                    Bitvector32Term::Constant(right as i32 as u32),
                ))
            }
            _ => SignedConstantResolution::Unknown,
        };
    }
    match term {
        Bitvector32Term::BitwiseNot(value) => operand(value).map(|value| {
            Bitvector32Term::bitwise_not(Bitvector32Term::Constant(value as i32 as u32))
        }),
        // The conversion's own constant fold: a byte constant `c` in
        // `0..=255` converts to its two's-complement value, and a constant
        // outside the byte range stays unfolded (`Unknown`).
        term => match word_cast_operand(term) {
            Some((value, source, destination)) => operand(value).map(|value| {
                Bitvector32Term::machine_integer_cast(
                    source,
                    destination,
                    Bitvector32Term::Constant(value as i32 as u32),
                )
            }),
            None => SignedConstantResolution::Unknown,
        },
    }
}

/// The memory-blind fingerprint of the pointer a load term reads, if the
/// term is a load or a registered load variable.
pub(in crate::kernel) fn load_key(term: &Bitvector32Term) -> Option<(u64, Bitvector32Term)> {
    let viewed = crate::kernel::eval::viewed_as_memory_load(term)?;
    let Bitvector32Term::MemoryLoad(_, pointer, _) = &viewed else {
        return None;
    };
    Some((memory_blind_pointer_fingerprint(pointer), viewed))
}

impl TermClasses {
    pub(super) fn mark_scalar_conflict(&mut self, id: u64) {
        let mut pending = vec![id];
        while let Some(id) = pending.pop() {
            let root = self.root(id);
            if self.scalar_conflicts.contains(&root) {
                continue;
            }
            self.scalar_conflicts = self.scalar_conflicts.with_value(root);
            if let Some(uses) = self.constant_uses.get(&root) {
                pending.extend(uses.iter().copied());
            }
        }
    }
}
