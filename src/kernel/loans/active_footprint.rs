//! Retained resource descriptor for active loan backing. Updates follow one
//! fixed-width loan-id path; access requirements clone only the root descriptor.
use super::{CMemoryRange, CResource, LoanId};
use std::sync::Arc;

#[derive(Clone, Debug, Default)]
pub(super) struct ActiveFootprint(Option<Arc<Node>>);

#[derive(Debug)]
struct Node {
    resource: CResource,
    children: [Option<Arc<Node>>; 2],
}

impl PartialEq for ActiveFootprint {
    fn eq(&self, other: &Self) -> bool {
        self.resource() == other.resource()
    }
}
impl Eq for ActiveFootprint {}
impl std::hash::Hash for ActiveFootprint {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.resource(), state);
    }
}

impl ActiveFootprint {
    pub(super) fn resource(&self) -> CResource {
        self.0
            .as_ref()
            .map_or(CResource::Emp, |node| node.resource.clone())
    }

    pub(super) fn with_loan(&self, loan: LoanId, ranges: &[CMemoryRange]) -> Self {
        let mut resources = ranges.iter().map(|range| CResource::Memory(range.clone()));
        let resource = resources
            .next()
            .map(|first| resources.fold(first, CResource::star));
        Self(update(self.0.as_ref(), loan.ordinal, 64, resource.as_ref()))
    }

    pub(super) fn without_loan(&self, loan: LoanId) -> Self {
        Self(update(self.0.as_ref(), loan.ordinal, 64, None))
    }
}

fn update(
    node: Option<&Arc<Node>>,
    key: u64,
    remaining: u32,
    resource: Option<&CResource>,
) -> Option<Arc<Node>> {
    crate::instrumentation::record_deterministic_work(1);
    if remaining == 0 {
        return resource.map(|resource| {
            Arc::new(Node {
                resource: resource.clone(),
                children: [None, None],
            })
        });
    }
    if node.is_none() && resource.is_none() {
        return None;
    }
    let mut children = node.map_or([None, None], |node| node.children.clone());
    let side = ((key >> (remaining - 1)) & 1) as usize;
    children[side] = update(children[side].as_ref(), key, remaining - 1, resource);
    let resource = match (&children[0], &children[1]) {
        (None, None) => return None,
        (Some(node), None) | (None, Some(node)) => node.resource.clone(),
        (Some(left), Some(right)) => CResource::star(left.resource.clone(), right.resource.clone()),
    };
    Some(Arc::new(Node { resource, children }))
}
