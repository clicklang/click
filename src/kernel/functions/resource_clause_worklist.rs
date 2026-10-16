//! The indexes a contract section's resource-clause worklist uses to wake a clause when an earlier clause supplies the memory it waits on.

use super::*;

/// Canonical segment-tree decomposition of `[start, end)`.  A range is
/// represented by O(32) aligned nodes, rather than by its cells.
pub(super) fn resource_clause_interval_nodes(
    space: &ResourceClauseIntervalSpace,
    start: i64,
    end: i64,
) -> Option<Vec<ResourceClauseIntervalNode>> {
    let mut start = resource_clause_biased_coordinate(start)?;
    let end = resource_clause_biased_coordinate(end)?;
    if start >= end {
        return None;
    }
    let mut nodes = Vec::new();
    while start < end {
        let alignment = if start == 0 {
            32
        } else {
            start.trailing_zeros().min(32)
        };
        let remaining = end - start;
        let magnitude = 63 - remaining.leading_zeros();
        let level = alignment.min(magnitude).min(32) as u8;
        let node_start = resource_clause_interval_node_start(start, level);
        nodes.push(resource_clause_interval_node(space, level, node_start));
        start += 1u64 << level;
    }
    Some(nodes)
}

pub(super) fn resource_clause_interval_node_ancestors(
    node: &ResourceClauseIntervalNode,
) -> Vec<ResourceClauseIntervalNode> {
    (node.level..=32)
        .map(|level| {
            resource_clause_interval_node(
                &node.space,
                level,
                resource_clause_interval_node_start(u64::from(node.start), level),
            )
        })
        .collect()
}

pub(super) fn resource_clause_interval_node_bounds(
    node: &ResourceClauseIntervalNode,
) -> (u64, u64) {
    let start = u64::from(node.start);
    (start, start + (1u64 << node.level))
}

impl ResourceClauseIntervalIndex {
    pub(super) fn insert(
        &mut self,
        waiter: ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            self.exact
                .entry(node.clone())
                .or_default()
                .insert(waiter.clone());
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                self.subtree
                    .entry(ancestor)
                    .or_default()
                    .insert(waiter.clone());
            }
        }
    }

    pub(super) fn remove(
        &mut self,
        waiter: &ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            let remove_exact = self.exact.get_mut(&node).is_some_and(|waiters| {
                waiters.remove(waiter);
                waiters.is_empty()
            });
            if remove_exact {
                self.exact.remove(&node);
            }
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                let remove_subtree = self.subtree.get_mut(&ancestor).is_some_and(|waiters| {
                    waiters.remove(waiter);
                    waiters.is_empty()
                });
                if remove_subtree {
                    self.subtree.remove(&ancestor);
                }
            }
        }
    }

    pub(super) fn add_candidates(
        waiters: &BTreeSet<ResourceClauseIntervalWaiter>,
        candidates: &mut BTreeSet<usize>,
    ) {
        candidates.extend(waiters.iter().map(|waiter| waiter.clause));
    }

    pub(super) fn query_node(
        &self,
        node: &ResourceClauseIntervalNode,
        query_start: u64,
        query_end: u64,
        candidates: &mut BTreeSet<usize>,
    ) {
        let (node_start, node_end) = resource_clause_interval_node_bounds(node);
        if node_end <= query_start || query_end <= node_start {
            return;
        }
        if let Some(waiters) = self.exact.get(node) {
            Self::add_candidates(waiters, candidates);
        }
        if query_start <= node_start && node_end <= query_end {
            if let Some(waiters) = self.subtree.get(node) {
                Self::add_candidates(waiters, candidates);
            }
            return;
        }
        if node.level == 0 {
            return;
        }
        let child_level = node.level - 1;
        let left = resource_clause_interval_node(&node.space, child_level, node.start);
        let right_start = (u64::from(node.start) + (1u64 << child_level)) as u32;
        let right = resource_clause_interval_node(&node.space, child_level, right_start);
        self.query_node(&left, query_start, query_end, candidates);
        self.query_node(&right, query_start, query_end, candidates);
    }

    pub(super) fn candidates_for_fact(&self, fact: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = BTreeSet::new();
        let Some(range) = fact.memory_range() else {
            return candidates;
        };
        let Some((space, start, end)) = resource_clause_concrete_memory_interval(range) else {
            return candidates;
        };
        let Some(query_start) = resource_clause_biased_coordinate(start) else {
            return candidates;
        };
        let Some(query_end) = resource_clause_biased_coordinate(end) else {
            return candidates;
        };
        let root = resource_clause_interval_node(&space, 32, 0);
        self.query_node(&root, query_start, query_end, &mut candidates);
        candidates
    }
}

pub(super) fn resource_clause_coarse_keys(
    fact: &CResourceFact,
) -> Vec<ResourceClauseDependencyKey> {
    let mut keys = vec![ResourceClauseDependencyKey::Fact(fact.clone())];
    if let Some(range) = fact.memory_range() {
        keys.push(ResourceClauseDependencyKey::MemoryBase(
            range.base().clone(),
        ));
        keys.push(ResourceClauseDependencyKey::MemoryBlock(
            range.base().block.clone(),
        ));
    }
    keys
}

impl ResourceClauseWaiterIndex {
    pub(super) fn register(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                self.coarse
                    .entry(ResourceClauseDependencyKey::Fact(dependency.clone()))
                    .or_default()
                    .insert(clause);
                self.concrete_block_fallback
                    .entry(space.block.clone())
                    .or_default()
                    .insert(waiter.clone());
                self.intervals.insert(waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    self.coarse.entry(key).or_default().insert(clause);
                }
            }
        }
    }

    pub(super) fn unregister(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                let key = ResourceClauseDependencyKey::Fact(dependency.clone());
                let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                    clauses.remove(&clause);
                    clauses.is_empty()
                });
                if remove_key {
                    self.coarse.remove(&key);
                }
                let remove_block = self
                    .concrete_block_fallback
                    .get_mut(&space.block)
                    .is_some_and(|waiters| {
                        waiters.remove(&waiter);
                        waiters.is_empty()
                    });
                if remove_block {
                    self.concrete_block_fallback.remove(&space.block);
                }
                self.intervals.remove(&waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                        clauses.remove(&clause);
                        clauses.is_empty()
                    });
                    if remove_key {
                        self.coarse.remove(&key);
                    }
                }
            }
        }
    }

    pub(super) fn candidates_for_supplied(&self, supplied: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = self.intervals.candidates_for_fact(supplied);
        // Concrete supplied facts use only exact/interval events.  The
        // fallback below is deliberately reserved for symbolic or otherwise
        // un-normalizable supplied memory: scanning concrete waiters in one
        // explicit symbolic block event is conservative and bounded by that
        // event's block-local waiter set, while concrete same-block events
        // retain their interval-sensitive work curve.
        if supplied
            .memory_range()
            .and_then(resource_clause_concrete_memory_interval)
            .is_none()
            && let Some(range) = supplied.memory_range()
            && let Some(waiters) = self.concrete_block_fallback.get(&range.base().block)
        {
            ResourceClauseIntervalIndex::add_candidates(waiters, &mut candidates);
        }
        for key in resource_clause_coarse_keys(supplied) {
            if let Some(clauses) = self.coarse.get(&key) {
                candidates.extend(clauses.iter().copied());
            }
        }
        candidates
    }
}

pub(super) fn resource_clause_register_waiters(
    index: usize,
    missing: Vec<CResourceFact>,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let mut unique = Vec::new();
    for dependency in missing {
        if unique.contains(&dependency) {
            continue;
        }
        unique.push(dependency.clone());
    }
    waiters.register(index, &unique);
    dependencies[index] = unique;
}

pub(super) fn resource_clause_unregister_waiters(
    index: usize,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let previous = std::mem::take(&mut dependencies[index]);
    waiters.unregister(index, &previous);
}

pub(super) fn resource_clause_enqueue_waiters(
    supplied: &CResourceFact,
    assumptions: &PureFactContext,
    section_supply: &ResourceContext,
    evaluated: &[Option<CResourceFact>],
    queued: &mut [bool],
    pending: &mut VecDeque<usize>,
    dependencies: &[Vec<CResourceFact>],
    waiters: &ResourceClauseWaiterIndex,
) {
    let candidates = waiters.candidates_for_supplied(supplied);
    for index in candidates {
        if evaluated[index].is_none()
            && !queued[index]
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
}
