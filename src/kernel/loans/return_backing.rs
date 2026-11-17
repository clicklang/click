//! Producer-maintained description indexes for selected return loan sources.
use super::*;
use crate::kernel::ResourceFamily;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct PermittedDescriptions {
    facts: imbl::Vector<ResourceFact>,
    exact: PersistentMap<Resource, usize>,
    families: PersistentMap<ResourceFamily, Option<usize>>,
}

impl PermittedDescriptions {
    pub(super) fn first(&self) -> Option<&ResourceFact> {
        self.facts.front()
    }
    pub(super) fn iter(&self) -> impl Iterator<Item = &ResourceFact> {
        self.facts.iter()
    }
    pub(super) fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
    pub(super) fn contains(&self, fact: &ResourceFact) -> bool {
        self.exact
            .get(fact.resource())
            .and_then(|index| self.facts.get(*index))
            == Some(fact)
    }
    pub(super) fn push(&mut self, fact: ResourceFact) {
        crate::instrumentation::record_deterministic_work(1);
        let index = self.facts.len();
        if !self.exact.contains_key(fact.resource()) {
            self.exact = self.exact.with_inserted(fact.resource().clone(), index);
            let candidate = if self.families.contains_key(&fact.family()) {
                None
            } else {
                Some(index)
            };
            self.families = self.families.with_inserted(fact.family(), candidate);
        }
        self.facts.push_back(fact);
    }
    pub(super) fn exact_candidate(&self, required: &ResourceFact) -> Option<&ResourceFact> {
        self.exact
            .get(required.resource())
            .and_then(|index| self.facts.get(*index))
    }
    pub(super) fn candidate(&self, required: &ResourceFact) -> Option<&ResourceFact> {
        crate::instrumentation::record_deterministic_work(1);
        let index = self
            .exact
            .get(required.resource())
            .copied()
            .or_else(|| self.families.get(&required.family()).copied().flatten())?;
        self.facts.get(index)
    }
}
impl From<Vec<ResourceFact>> for PermittedDescriptions {
    fn from(facts: Vec<ResourceFact>) -> Self {
        facts.into_iter().collect()
    }
}
impl FromIterator<ResourceFact> for PermittedDescriptions {
    fn from_iter<T: IntoIterator<Item = ResourceFact>>(facts: T) -> Self {
        let mut result = Self::default();
        for fact in facts {
            result.push(fact);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn permission_updates_are_indexed_and_branch_local() {
        let a = ResourceFact::view_memory(MemoryRange::new(
            Address::symbolic(Variable(8_910_001)),
            0u32.into(),
            1u32.into(),
        ));
        let b = ResourceFact::view_memory(MemoryRange::new(
            Address::symbolic(Variable(8_910_002)),
            0u32.into(),
            1u32.into(),
        ));
        let parent: PermittedDescriptions = vec![a.clone()].into();
        let mut child = parent.clone();
        child.push(b.clone());
        assert_eq!(parent.candidate(&b), Some(&a));
        assert_eq!(child.candidate(&b), Some(&b));
        let missing = ResourceFact::view_memory(MemoryRange::new(
            Address::symbolic(Variable(8_910_003)),
            0u32.into(),
            1u32.into(),
        ));
        assert!(child.candidate(&missing).is_none());
        assert_eq!(parent.candidate(&missing), Some(&a));
        assert!(!parent.contains(&b));
        assert!(child.contains(&b));
    }
    mod scaling_tests {
        include!("../../scaling_tests/kernel/loans/return_backing.rs");
    }
}
