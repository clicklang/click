//! Block declarations with a persistent index of declared scalar storage.
//! Read access delegates to the map; all edits maintain the index at source.
use super::*;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, Default)]
pub(crate) struct MemoryBlocks {
    entries: HashedOrdMap<AddressBase, MemoryBlock>,
    scalars: HashedOrdSet<AddressBase>,
}

impl std::ops::Deref for MemoryBlocks {
    type Target = HashedOrdMap<AddressBase, MemoryBlock>;
    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}
impl PartialEq for MemoryBlocks {
    fn eq(&self, other: &Self) -> bool {
        self.entries == other.entries
    }
}
impl Eq for MemoryBlocks {}
impl Hash for MemoryBlocks {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.entries.hash(state);
    }
}
impl MemoryBlocks {
    pub(crate) fn scalar_blocks(&self) -> impl Iterator<Item = &AddressBase> {
        self.scalars
            .iter()
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
    }
    pub(crate) fn insert(&mut self, key: AddressBase, value: MemoryBlock) -> Option<MemoryBlock> {
        if value.declared_scalar_type.is_some() {
            self.scalars.insert(key.clone());
        } else {
            self.scalars.remove(&key);
        }
        self.entries.insert(key, value)
    }
    pub(crate) fn remove(&mut self, key: &AddressBase) -> Option<MemoryBlock> {
        self.scalars.remove(key);
        self.entries.remove(key)
    }
    pub(crate) fn get_or_insert(&mut self, key: AddressBase, value: MemoryBlock) -> &MemoryBlock {
        if !self.entries.contains_key(&key) {
            self.insert(key.clone(), value);
        }
        self.entries.get(&key).expect("entry was just ensured")
    }
    /// Restore changed declarations while retaining blocks absent from `other`.
    /// Both the map and scalar subset are edited by the same selected delta.
    pub(crate) fn overwrite_with(&mut self, other: &Self) {
        let changed = self
            .entries
            .diff(&other.entries)
            .filter_map(|change| match change {
                HashedOrdMapChange::Removed(_) => None,
                HashedOrdMapChange::Added(key) | HashedOrdMapChange::Changed(key) => Some((
                    key.clone(),
                    other.get(key).expect("changed block exists").clone(),
                )),
            })
            .collect::<Vec<_>>();
        for (key, value) in changed {
            self.insert(key, value);
        }
    }
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&AddressBase, &MemoryBlock) -> bool) {
        // The existing whole-map operation charges each visited declaration.
        let scalars = &mut self.scalars;
        self.entries.retain(|key, value| {
            let retained = keep(key, value);
            if !retained {
                scalars.remove(key);
            }
            retained
        });
    }
    pub(crate) fn union_of_arms<'a>(
        &self,
        others: impl Iterator<Item = &'a Self>,
    ) -> Result<Self, AddressBase> {
        let mut union = self.clone();
        for other in others {
            for change in self.entries.diff(&other.entries) {
                match change {
                    HashedOrdMapChange::Removed(_) => {}
                    HashedOrdMapChange::Changed(key) => return Err(key.clone()),
                    HashedOrdMapChange::Added(key) => {
                        let value = other.get(key).expect("an added key is held").clone();
                        if let Some(existing) = union.insert(key.clone(), value.clone())
                            && existing != value
                        {
                            return Err(key.clone());
                        }
                    }
                }
            }
        }
        Ok(union)
    }
}
impl FromIterator<(AddressBase, MemoryBlock)> for MemoryBlocks {
    fn from_iter<T: IntoIterator<Item = (AddressBase, MemoryBlock)>>(iter: T) -> Self {
        let mut blocks = Self::default();
        for (key, value) in iter {
            blocks.insert(key, value);
        }
        blocks
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_index_tracks_lifetime_replacement_and_branch_isolation() {
        let scalar = OldAddress::symbolic(Variable(9_392_001)).base;
        let heap = OldAddress::symbolic(Variable(9_392_002)).base;
        let memory = SymbolicMemory::new()
            .with_declared_scalar_block(scalar.clone(), 4, ProgramType::Int32)
            .with_block(heap.clone(), 64);
        assert_eq!(
            memory.blocks.scalar_blocks().collect::<Vec<_>>(),
            vec![&scalar]
        );
        let retired = memory.without_local_block(&scalar);
        assert_eq!(retired.blocks.scalar_blocks().count(), 0);
        assert!(memory.blocks.contains_key(&scalar));
        assert_eq!(memory.blocks.scalar_blocks().count(), 1);
        let frozen = memory.clone().freeze_declared_scalar(&scalar);
        assert_eq!(frozen.blocks.scalar_blocks().count(), 1);
        let mut branch = (*memory.blocks).clone();
        branch.insert(scalar.clone(), MemoryBlock::new(4));
        assert_eq!(branch.scalar_blocks().count(), 0);
        branch.insert(scalar.clone(), memory.blocks.get(&scalar).unwrap().clone());
        branch.retain(|key, _| key != &scalar);
        assert_eq!(branch.scalar_blocks().count(), 0);
        assert!(branch.contains_key(&heap));
        assert_eq!(memory.blocks.scalar_blocks().count(), 1);
    }

    #[test]
    fn scalar_index_survives_arm_union_and_selected_projection() {
        let a = OldAddress::symbolic(Variable(9_392_003)).base;
        let b = OldAddress::symbolic(Variable(9_392_004)).base;
        let first =
            SymbolicMemory::new().with_declared_scalar_block(a.clone(), 4, ProgramType::Int32);
        let second = first
            .clone()
            .with_declared_scalar_block(b.clone(), 4, ProgramType::Int32);
        let joined = first
            .blocks
            .union_of_arms(std::iter::once(&*second.blocks))
            .unwrap();
        assert_eq!(joined.scalar_blocks().count(), 2);
        assert_eq!(first.blocks.scalar_blocks().count(), 1);
        let projected =
            std::iter::once((b.clone(), joined.get(&b).unwrap().clone())).collect::<MemoryBlocks>();
        assert_eq!(projected.scalar_blocks().collect::<Vec<_>>(), vec![&b]);
        let mut conflicting = joined.clone();
        conflicting.insert(a.clone(), MemoryBlock::new(4));
        assert_eq!(
            joined.union_of_arms(std::iter::once(&conflicting)),
            Err(a.clone())
        );
        let mut restored = joined.clone();
        restored.overwrite_with(&conflicting);
        assert_eq!(restored.scalar_blocks().collect::<Vec<_>>(), vec![&b]);
        restored.overwrite_with(&first.blocks);
        assert_eq!(restored.scalar_blocks().count(), 2);
        assert_eq!(joined.scalar_blocks().count(), 2);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/memory_blocks.rs");
}
