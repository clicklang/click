//! Persistent parent and weight storage for the equality graph's local node IDs.

use crate::id_hash::U64BuildHasher;
use std::num::NonZeroU64;
use std::sync::Arc;

const PAGE_LEN: usize = 32;

#[derive(Clone, Copy)]
struct ClassLink {
    // Registered node IDs are indices, so the parent ID plus one fits.
    parent: Option<NonZeroU64>,
    weight: usize,
}

const IMPLICIT_LINK: ClassLink = ClassLink {
    parent: None,
    weight: 1,
};

type Page = [ClassLink; PAGE_LEN];

#[derive(Clone, Default)]
pub(super) struct ClassLinks {
    // The sparse directory shares its trie across forks. A write copies the
    // directory path and the touched page only if they are shared.
    pages: imbl::GenericHashMap<u64, Arc<Page>, U64BuildHasher, imbl::shared_ptr::DefaultSharedPtr>,
    // Union only adds parent links. Weight-only pages do not imply a merge.
    has_parents: bool,
}

impl ClassLinks {
    fn get(&self, id: u64) -> ClassLink {
        self.pages
            .get(&(id / PAGE_LEN as u64))
            .map_or(IMPLICIT_LINK, |page| page[(id % PAGE_LEN as u64) as usize])
    }

    fn entry(&mut self, id: u64) -> &mut ClassLink {
        let page = self
            .pages
            .entry(id / PAGE_LEN as u64)
            .or_insert_with(|| Arc::new([IMPLICIT_LINK; PAGE_LEN]));
        &mut Arc::make_mut(page)[(id % PAGE_LEN as u64) as usize]
    }

    pub(super) fn parent(&self, id: u64) -> Option<u64> {
        self.get(id).parent.map(|parent| parent.get() - 1)
    }

    pub(super) fn has_parents(&self) -> bool {
        self.has_parents
    }

    pub(super) fn weight(&self, id: u64) -> usize {
        self.get(id).weight
    }

    pub(super) fn set_weight(&mut self, id: u64, weight: usize) {
        self.entry(id).weight = weight;
    }

    pub(super) fn merge(&mut self, moved: u64, kept: u64, weight: usize) {
        let parent = NonZeroU64::new(kept + 1).expect("registered parent node ID");
        *self.entry(moved) = ClassLink {
            parent: Some(parent),
            weight: 1,
        };
        self.entry(kept).weight = weight;
        self.has_parents = true;
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/equality_graph/terms/class_links.rs");
}
