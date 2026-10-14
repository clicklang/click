//! Difference logic over the path's integer facts: a persistent graph of
//! constraints `x - y <= c` with a constant interval on every node, extended
//! fact by fact and queried by reading bounds and edges.
//!
//! Nodes are `(domain, term)` pairs whose values are mathematical integers,
//! so values of different widths can be related. A constant is never a node:
//! a bound `x <= 4` narrows `x`'s interval instead of joining `x` to a node
//! `4`, so facts about unrelated values never meet at a shared constant. A
//! term `x + k` is linked to `x` only once `x`'s interval shows the sum
//! cannot wrap in its domain.
//!
//! Insertion checks the new edge for a negative cycle among the nodes it
//! reaches, then propagates intervals from the edge's endpoints. Its work
//! is the component the edge joins, not the graph. A query compares stored
//! intervals and, between two nodes, reads the shortest path inside the
//! source's component. Every answer follows from the inserted facts by
//! difference logic; a contradictory graph answers only that an overflow is
//! absent, which holds vacuously on a dead path.
//!
//! See `issues/difference-logic.md`.

use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, PointerOffsetTerm};
use crate::persistent::PersistentMap;

/// The integer domain a node's value ranges over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Domain {
    Int32,
    Int64,
    UInt64,
}

impl Domain {
    fn range(self) -> (i128, i128) {
        match self {
            Domain::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
            Domain::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
            Domain::UInt64 => (0, i128::from(u64::MAX)),
        }
    }
}

type NodeId = u32;

/// A value as `node + offset`, or the constant `offset` when `node` is
/// `None`.
type Affine = (Option<NodeId>, i128);

/// A link a node waits for: `node = base + offset` once `base`'s interval
/// shows the value stays in `domain` (and is non-negative, for a conversion
/// that keeps only non-negative values).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PendingLink {
    offset: i128,
    domain: Domain,
    nonnegative: bool,
}

#[derive(Clone, Default)]
pub(crate) struct DifferenceGraph {
    nodes: PersistentMap<(Domain, Bitvector32Term), NodeId>,
    domains: PersistentMap<NodeId, Domain>,
    /// Tightened intervals; a node absent here ranges over its domain.
    bounds: PersistentMap<NodeId, (i128, i128)>,
    /// `from -> to -> w`: `to - from <= w`, the least `w` inserted.
    out_edges: PersistentMap<NodeId, PersistentMap<NodeId, i128>>,
    in_edges: PersistentMap<NodeId, PersistentMap<NodeId, i128>>,
    /// `base -> node -> link`: links waiting on `base`'s interval.
    pending: PersistentMap<NodeId, PersistentMap<NodeId, PendingLink>>,
    /// `node -> {c}`: `node != c`. An interval end landing on an excluded
    /// value steps past it, so `x != INT_MIN` beside `INT_MIN <= x` is
    /// `INT_MIN + 1 <= x`.
    excluded: PersistentMap<NodeId, crate::persistent::PersistentSet<i128>>,
    /// `node -> (x, t)` for each `t = x ^ MIN` whose sign case is still
    /// open, under both `x` and `t`: `t` is `x + MIN` when `x >= 0` and
    /// `x - MIN` when `x < 0`, so the sign of either decides the link.
    flips: PersistentMap<NodeId, (NodeId, NodeId)>,
    /// Nodes whose bound was not pushed along all their edges
    /// (`EDGE_LIMIT`): a neighbour's stored interval may miss it, so reads
    /// pull from these nodes.
    truncated: crate::persistent::PersistentSet<NodeId>,
    /// Each narrow integer cast's node and its operand's: `t ≡ v (mod m)`
    /// with `v` in the source type's range, linked as `t = v - k·m` once the
    /// two intervals leave one `k` (`resolve_casts`).
    cast_links: PersistentMap<NodeId, CastLink>,
    /// The casts waiting on each operand node.
    casts_of: PersistentMap<NodeId, crate::persistent::PersistentSet<NodeId>>,
    /// Pointer equality facts: a union-find over the pointer terms they
    /// name (`pointer_ids`, `pointer_parent`, `pointer_size`), with each
    /// class root's known-unequal pointers, so `p == null` and `q != null`
    /// give `p != q`.
    pointers: PointerClasses,
    /// Overflow conditions recorded false (`OverflowKey`).
    no_overflow: crate::persistent::PersistentSet<OverflowKey>,
    contradictory: bool,
    next: NodeId,
}

/// How many edges one bound's propagation, one cycle check, one path query
/// or one interval read follows, and how many waiting links one bound
/// examines. Past it the graph stays sound and answers less: a stored bound
/// is still true, only looser, and an unseen cycle leaves a dead path
/// undetected. A value many others are bounded by (an array length) then
/// costs the same however many there are.
pub(crate) const EDGE_LIMIT: usize = 32;

/// Charges and, in test builds, counts one unit of graph work.
fn charge() {
    crate::instrumentation::record_deterministic_work(1);
    #[cfg(test)]
    tests::GRAPH_WORK.with(|work| work.set(work.get() + 1));
}

impl DifferenceGraph {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Whether the inserted facts contradict each other.
    #[cfg(test)]
    pub(crate) fn is_contradictory(&self) -> bool {
        self.contradictory
    }

    fn domain(&self, node: NodeId) -> Domain {
        *self.domains.get(&node).expect("a node has a domain")
    }

    fn interval(&self, node: NodeId) -> (i128, i128) {
        self.bounds
            .get(&node)
            .copied()
            .unwrap_or_else(|| self.domain(node).range())
    }

    /// `node`'s stored interval narrowed by one hop from neighbours whose
    /// bound the bounded propagation did not push to it (`truncated`):
    /// `node - p <= w` bounds `node <= hi(p) + w`, and `s - node <= w`
    /// bounds `node >= lo(s) - w`. With no truncated push it is the stored
    /// interval.
    fn read_interval(&self, node: NodeId) -> (i128, i128) {
        let (mut low, mut high) = self.interval(node);
        if self.truncated.is_empty() {
            return (low, high);
        }
        if let Some(edges) = self.in_edges.get(&node) {
            for (previous, weight) in edges.iter().take(EDGE_LIMIT) {
                charge();
                if self.truncated.contains(previous) {
                    high = high.min(self.interval(*previous).1.saturating_add(*weight));
                }
            }
        }
        if let Some(edges) = self.out_edges.get(&node) {
            for (next, weight) in edges.iter().take(EDGE_LIMIT) {
                charge();
                if self.truncated.contains(next) {
                    low = low.max(self.interval(*next).0.saturating_sub(*weight));
                }
            }
        }
        (low, high)
    }

    fn affine_interval(&self, (node, offset): Affine) -> (i128, i128) {
        match node {
            None => (offset, offset),
            Some(node) => {
                let (low, high) = self.read_interval(node);
                (low + offset, high + offset)
            }
        }
    }

    /// Records a true or false condition fact. A fact difference logic does
    /// not express is ignored.
    pub(crate) fn assume_condition(&mut self, condition: &ConditionTerm, value: bool) {
        if let ConditionTerm::PointerEqual(a, b) = condition {
            if !self.pointers.assume(a, b, value) {
                self.contradictory = true;
            }
            return;
        }
        if let Some(equality) = offset_equality(condition) {
            self.assume_condition(&equality, value);
            return;
        }
        if value
            && let ConditionTerm::Bitvector32Equal(a, b) | ConditionTerm::Bitvector64Equal(a, b) =
                condition
            && self.alias_equality(condition, a, b)
        {
            return;
        }
        if let Some((operation, domain, a, b, commutative)) = overflow_parts(condition) {
            if !value {
                let a = self.affine(domain, a);
                let b = self.affine(domain, b);
                charge();
                self.no_overflow =
                    self.no_overflow
                        .with_value(overflow_key(operation, a, b, commutative));
            }
            return;
        }
        if !value
            && let ConditionTerm::Bitvector32Equal(a, b) | ConditionTerm::Bitvector64Equal(a, b) =
                condition
        {
            self.exclude(condition, a, b);
            return;
        }
        for (domain, lower, upper, strict) in condition_orders(condition, value) {
            if self.contradictory {
                return;
            }
            let lower = self.affine(domain, &lower);
            let upper = self.affine(domain, &upper);
            // lower - upper <= -strict
            self.constrain(upper, lower, -i128::from(strict));
        }
    }

    /// Records `a != b` when one side is a constant and the other a node
    /// plus an offset: the node excludes one value, and its interval steps
    /// off that value if it is an end.
    fn exclude(&mut self, condition: &ConditionTerm, a: &Bitvector32Term, b: &Bitvector32Term) {
        let domains: &[Domain] = if matches!(condition, ConditionTerm::Bitvector32Equal(..)) {
            &[Domain::Int32]
        } else {
            &[Domain::Int64, Domain::UInt64]
        };
        for domain in domains {
            let (term, value) = match (constant(*domain, a), constant(*domain, b)) {
                (None, Some(value)) => (a, value),
                (Some(value), None) => (b, value),
                _ => continue,
            };
            let (Some(node), offset) = self.affine(*domain, term) else {
                continue;
            };
            charge();
            let excluded = self.excluded.get(&node).cloned().unwrap_or_default();
            self.excluded
                .insert(node, excluded.with_value(value - offset));
            self.tighten(node, None, None);
        }
    }

    /// Whether `node != value` was recorded.
    fn excludes(&self, node: NodeId, value: i128) -> bool {
        self.excluded
            .get(&node)
            .is_some_and(|excluded| excluded.contains(&value))
    }

    /// Records a true equality between a term the graph has no node for and
    /// another value by naming that value's node for the new term, instead
    /// of joining two nodes by a pair of edges. Every term equated to one
    /// value is then that value's node, so a value with many names stays one
    /// node and its component does not grow with them. Declines (returns
    /// `false`) when neither side is such a term, or when the new term is a
    /// sum or conversion whose own link it would lose.
    fn alias_equality(
        &mut self,
        condition: &ConditionTerm,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
    ) -> bool {
        let domains: &[Domain] = if matches!(condition, ConditionTerm::Bitvector32Equal(..)) {
            &[Domain::Int32]
        } else {
            &[Domain::Int64, Domain::UInt64]
        };
        let fresh = |graph: &Self, term: &Bitvector32Term| {
            domains.iter().all(|domain| {
                constant(*domain, term).is_none()
                    && link_parts(*domain, term).is_none()
                    && !graph.nodes.contains_key(&(*domain, term.clone()))
            })
        };
        let (new, existing) = if fresh(self, a) {
            (a, b)
        } else if fresh(self, b) {
            (b, a)
        } else {
            return false;
        };
        let targets = domains
            .iter()
            .map(|domain| (*domain, self.affine(*domain, existing)))
            .collect::<Vec<_>>();
        if targets
            .iter()
            .any(|(_, (node, offset))| node.is_none() || *offset != 0)
        {
            // A constant, or an offset from a node: the ordinary edges say it.
            return false;
        }
        for (domain, (node, _)) in targets {
            charge();
            self.nodes
                .insert((domain, new.clone()), node.expect("checked above"));
        }
        true
    }

    /// `to - from <= weight`.
    fn constrain(&mut self, from: Affine, to: Affine, weight: i128) {
        // (to.node + to.offset) - (from.node + from.offset) <= weight
        let weight = weight - to.1 + from.1;
        match (from.0, to.0) {
            (None, None) => {
                if 0 > weight {
                    self.contradictory = true;
                }
            }
            (None, Some(to)) => self.tighten(to, None, Some(weight)),
            (Some(from), None) => self.tighten(from, Some(-weight), None),
            (Some(from), Some(to)) if from == to => {
                if weight < 0 {
                    self.contradictory = true;
                }
            }
            (Some(from), Some(to)) => self.add_edge(from, to, weight),
        }
    }

    fn add_edge(&mut self, from: NodeId, to: NodeId, weight: i128) {
        if self
            .out_edges
            .get(&from)
            .and_then(|edges| edges.get(&to))
            .is_some_and(|existing| *existing <= weight)
        {
            return;
        }
        // A path `to -> from` shorter than `-weight` closes a negative cycle.
        if self
            .shortest_from(to)
            .get(&from)
            .is_some_and(|distance| distance + weight < 0)
        {
            self.contradictory = true;
            return;
        }
        let out = self.out_edges.get(&from).cloned().unwrap_or_default();
        self.out_edges.insert(from, out.with_inserted(to, weight));
        let incoming = self.in_edges.get(&to).cloned().unwrap_or_default();
        self.in_edges
            .insert(to, incoming.with_inserted(from, weight));
        let (_, from_high) = self.interval(from);
        let (to_low, _) = self.interval(to);
        self.tighten(to, None, Some(from_high.saturating_add(weight)));
        self.tighten(from, Some(to_low.saturating_sub(weight)), None);
    }

    /// Narrows `node`'s interval and propagates along its edges: a lower
    /// upper bound flows forward (`m - n <= w` bounds `m <= hi(n) + w`), a
    /// higher lower bound backward (`n - p <= w` bounds `p >= lo(n) - w`).
    fn tighten(&mut self, node: NodeId, low: Option<i128>, high: Option<i128>) {
        let mut work = vec![(node, low, high)];
        // Edges this propagation may still follow (`EDGE_LIMIT`).
        let mut budget = EDGE_LIMIT;
        while let Some((node, low, high)) = work.pop() {
            if self.contradictory {
                return;
            }
            charge();
            let (old_low, old_high) = self.interval(node);
            let mut new_low = low.map_or(old_low, |low| low.max(old_low));
            let mut new_high = high.map_or(old_high, |high| high.min(old_high));
            if let Some(excluded) = self.excluded.get(&node) {
                // Each step passes one recorded disequality.
                while new_low <= new_high && excluded.contains(&new_low) {
                    charge();
                    new_low += 1;
                }
                while new_low <= new_high && excluded.contains(&new_high) {
                    charge();
                    new_high -= 1;
                }
            }
            if (new_low, new_high) == (old_low, old_high) {
                continue;
            }
            if new_low > new_high {
                self.contradictory = true;
                return;
            }
            self.bounds.insert(node, (new_low, new_high));
            if new_high < old_high
                && let Some(edges) = self.out_edges.get(&node)
            {
                if edges.len() > budget {
                    self.truncated = self.truncated.with_value(node);
                }
                for (next, weight) in edges.iter().take(budget) {
                    budget -= 1;
                    work.push((*next, None, Some(new_high.saturating_add(*weight))));
                }
            }
            if new_low > old_low
                && let Some(edges) = self.in_edges.get(&node)
            {
                if edges.len() > budget {
                    self.truncated = self.truncated.with_value(node);
                }
                for (previous, weight) in edges.iter().take(budget) {
                    budget -= 1;
                    work.push((*previous, Some(new_low.saturating_sub(*weight)), None));
                }
            }
            self.resolve_pending(node);
            self.resolve_flip(node);
            self.resolve_casts(node);
        }
    }

    /// Settles the sign case of the `x ^ MIN` pair `node` belongs to, if
    /// either side's interval now decides it: a known sign of `x` links `t`
    /// to `x`, and a known sign of `t` bounds `x`, whose tightening links
    /// them in turn.
    fn resolve_flip(&mut self, node: NodeId) {
        let Some((base, flipped)) = self.flips.get(&node).copied() else {
            return;
        };
        charge();
        let min = self.domain(flipped).range().0;
        let (base_low, base_high) = self.interval(base);
        let offset = if base_low >= 0 {
            Some(min)
        } else if base_high < 0 {
            Some(-min)
        } else {
            None
        };
        if let Some(offset) = offset {
            self.flips.remove(&base);
            self.flips.remove(&flipped);
            // flipped = base + offset
            self.constrain((Some(base), 0), (Some(flipped), 0), offset);
            self.constrain((Some(flipped), 0), (Some(base), 0), -offset);
            return;
        }
        let (low, high) = self.interval(flipped);
        if high < 0 {
            self.tighten(base, Some(0), None);
        } else if low >= 0 {
            self.tighten(base, None, Some(-1));
        }
    }

    /// Links each cast `node` belongs to, as operand or as cast, whose two
    /// intervals now leave a single multiple of the modulus between them.
    fn resolve_casts(&mut self, node: NodeId) {
        let mut casts: Vec<NodeId> = self
            .casts_of
            .get(&node)
            .map(|casts| casts.iter().copied().take(EDGE_LIMIT).collect())
            .unwrap_or_default();
        if self.cast_links.contains_key(&node) {
            casts.push(node);
        }
        for cast in casts {
            charge();
            let Some(link) = self.cast_links.get(&cast).copied() else {
                continue;
            };
            let (v_low, v_high) = self.interval(link.base);
            if v_low < link.source.0 || v_high > link.source.1 {
                continue;
            }
            let (t_low, t_high) = self.interval(cast);
            // v - t = k·m with both in their intervals.
            let k_low = -((t_high - v_low).div_euclid(link.modulus));
            let k_high = (v_high - t_low).div_euclid(link.modulus);
            if k_low != k_high {
                continue;
            }
            self.cast_links.remove(&cast);
            if let Some(waiting) = self.casts_of.get(&link.base).cloned() {
                let waiting = waiting.without_value(&cast);
                if waiting.is_empty() {
                    self.casts_of.remove(&link.base);
                } else {
                    self.casts_of.insert(link.base, waiting);
                }
            }
            // cast = base - k·m
            let offset = -k_low * link.modulus;
            self.constrain((Some(link.base), 0), (Some(cast), 0), offset);
            self.constrain((Some(cast), 0), (Some(link.base), 0), -offset);
        }
    }

    /// Adds every link waiting on `base` whose value now provably stays in
    /// its domain.
    fn resolve_pending(&mut self, base: NodeId) {
        let Some(waiting) = self.pending.get(&base).cloned() else {
            return;
        };
        let (low, high) = self.interval(base);
        let mut remaining = waiting.clone();
        let mut linked = Vec::new();
        for (node, link) in waiting.iter().take(EDGE_LIMIT) {
            charge();
            if link_fits((low, high), link.offset, link.domain, link.nonnegative) {
                remaining = remaining.without_key(node);
                linked.push((*node, link.offset));
            }
        }
        if remaining.is_empty() {
            self.pending.remove(&base);
        } else {
            self.pending.insert(base, remaining);
        }
        for (node, offset) in linked {
            // node = base + offset
            self.constrain((Some(base), 0), (Some(node), 0), offset);
            self.constrain((Some(node), 0), (Some(base), 0), -offset);
        }
    }

    /// Shortest distances from `source` over at most `EDGE_LIMIT` edges it
    /// reaches (`distance[v]` bounds `v - source`). The caller has excluded
    /// negative cycles it could see, and the limit ends the relaxation in
    /// any case.
    fn shortest_from(&self, source: NodeId) -> std::collections::BTreeMap<NodeId, i128> {
        let mut distance = std::collections::BTreeMap::from([(source, 0i128)]);
        // First in, first out: with negative weights a stack can revisit a
        // node exponentially often; a queue relaxes in rounds.
        let mut work = std::collections::VecDeque::from([source]);
        let mut budget = EDGE_LIMIT;
        while let Some(node) = work.pop_front() {
            let Some(edges) = self.out_edges.get(&node) else {
                continue;
            };
            let base = distance[&node];
            for (next, weight) in edges.iter() {
                if budget == 0 {
                    // Each distance found is a real path's length, so a
                    // partial walk still bounds every node it reached.
                    return distance;
                }
                budget -= 1;
                charge();
                let candidate = base + weight;
                if distance.get(next).is_none_or(|known| candidate < *known) {
                    distance.insert(*next, candidate);
                    work.push_back(*next);
                }
            }
        }
        distance
    }

    /// The node for `term`, created with its pending links when new.
    fn node(&mut self, domain: Domain, term: &Bitvector32Term) -> NodeId {
        if let Some(node) = self.nodes.get(&(domain, term.clone())) {
            return *node;
        }
        let node = self.next;
        self.next += 1;
        self.nodes.insert((domain, term.clone()), node);
        self.domains.insert(node, domain);
        if let Some((value, source, destination, modulus)) = narrow_cast_parts(domain, term) {
            // A cast's value is always in its destination's range.
            self.tighten(node, Some(destination.0), Some(destination.1));
            if let (Some(base), 0) = self.affine(Domain::Int32, value) {
                self.cast_links.insert(
                    node,
                    CastLink {
                        base,
                        source,
                        modulus,
                    },
                );
                let waiting = self.casts_of.get(&base).cloned().unwrap_or_default();
                self.casts_of.insert(base, waiting.with_value(node));
                self.resolve_casts(node);
            }
        }
        if let Some(base) = sign_flip_base(domain, term) {
            match self.affine(domain, base) {
                (None, value) => {
                    let value = flip_sign(domain, value);
                    self.tighten(node, Some(value), Some(value));
                }
                (Some(base), 0) => {
                    self.flips.insert(base, (base, node));
                    self.flips.insert(node, (base, node));
                    self.resolve_flip(node);
                }
                // An offset base keeps the term opaque.
                (Some(_), _) => {}
            }
        }
        if let Some((base_domain, base, offset, nonnegative)) = link_parts(domain, term) {
            let base = self.affine(base_domain, base);
            match base {
                (None, constant) => {
                    // A constant base: the value is known when it fits.
                    let (min, max) = domain.range();
                    let value = constant + offset;
                    if value >= min && value <= max && (!nonnegative || constant >= 0) {
                        self.tighten(node, Some(value), Some(value));
                    }
                }
                (Some(base_node), base_offset) => {
                    let waiting = self.pending.get(&base_node).cloned().unwrap_or_default();
                    self.pending.insert(
                        base_node,
                        waiting.with_inserted(
                            node,
                            PendingLink {
                                offset: offset + base_offset,
                                domain,
                                nonnegative,
                            },
                        ),
                    );
                    self.resolve_pending(base_node);
                }
            }
        }
        node
    }

    /// `term` as a node and offset. A link its base's interval already
    /// justifies names the base directly rather than a new node, so the
    /// values `x + 1`, `x + 2`, ... share `x`'s node instead of each
    /// hanging an edge pair off it that every bound on `x` must walk.
    fn affine(&mut self, domain: Domain, term: &Bitvector32Term) -> Affine {
        if let Some(value) = constant(domain, term) {
            return (None, value);
        }
        if let Some(node) = self.nodes.get(&(domain, term.clone())) {
            return (Some(*node), 0);
        }
        if let Some((base_domain, base, offset, nonnegative)) = link_parts(domain, term) {
            let base = self.affine(base_domain, base);
            if base.0.is_some()
                && link_fits(self.affine_interval(base), offset, domain, nonnegative)
            {
                return (base.0, base.1 + offset);
            }
        }
        if let Some(base) = sign_flip_base(domain, term) {
            let base = self.affine(domain, base);
            if let Some(flipped) = self.known_flip(domain, base) {
                return flipped;
            }
        }
        (Some(self.node(domain, term)), 0)
    }

    /// `term` as known nodes and constants, without adding to the graph.
    /// A term not in the graph resolves through a link its base's interval
    /// already justifies; otherwise `None`.
    fn resolve(&self, domain: Domain, term: &Bitvector32Term) -> Option<Affine> {
        if let Some(value) = constant(domain, term) {
            return Some((None, value));
        }
        if let Some(node) = self.nodes.get(&(domain, term.clone())) {
            return Some((Some(*node), 0));
        }
        if let Some(base) = sign_flip_base(domain, term) {
            return self.known_flip(domain, self.resolve(domain, base)?);
        }
        let (base_domain, base, offset, nonnegative) = link_parts(domain, term)?;
        let base = self.resolve(base_domain, base)?;
        link_fits(self.affine_interval(base), offset, domain, nonnegative)
            .then_some((base.0, base.1 + offset))
    }

    /// `x ^ MIN` for `x` at `base`, when `x`'s sign is known.
    fn known_flip(&self, domain: Domain, base: Affine) -> Option<Affine> {
        let min = domain.range().0;
        match base {
            (None, value) => Some((None, flip_sign(domain, value))),
            (Some(_), _) => {
                let (low, high) = self.affine_interval(base);
                if low >= 0 {
                    Some((base.0, base.1 + min))
                } else if high < 0 {
                    Some((base.0, base.1 - min))
                } else {
                    None
                }
            }
        }
    }

    /// The least known upper bound on `to - from`, from intervals and from
    /// the shortest path inside `from`'s component.
    fn difference_bound(&self, from: Affine, to: Affine) -> i128 {
        let (_, to_high) = self.affine_interval(to);
        let (from_low, _) = self.affine_interval(from);
        let by_intervals = to_high - from_low;
        let by_path = match (from.0, to.0) {
            (Some(from_node), Some(to_node)) => self
                .shortest_from(from_node)
                .get(&to_node)
                .map(|distance| distance + to.1 - from.1),
            _ => None,
        };
        by_path.map_or(by_intervals, |path| path.min(by_intervals))
    }

    /// What the inserted facts decide about `condition`: its truth value,
    /// or `None` when difference logic leaves it open or the facts are
    /// contradictory.
    pub(crate) fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
        use ConditionTerm as C;
        if let C::Constant(value) = condition {
            return Some(*value);
        }
        if let C::PointerOffsetEqual(a, b) = condition
            && let Some(answer) = offset_mismatch(a, b)
        {
            return Some(answer);
        }
        if let C::PointerEqual(a, b) = condition {
            return self.pointers.decide(a, b);
        }
        if let C::PointerOffsetEqual(a, b) = condition
            && let Some(answer) = self.pointers.decide_offsets(a, b)
        {
            return Some(answer);
        }
        if let Some(equality) = offset_equality(condition) {
            return self.decide(&equality);
        }
        if self.contradictory {
            // No model satisfies the facts, so the path is dead and every
            // answer holds. Only the absence of overflow is given, the one
            // overflow answer this graph ever gives (see `decide_overflow`).
            return matches!(
                condition,
                C::Bitvector32SignedAddOverflows(..)
                    | C::Bitvector32SignedSubtractOverflows(..)
                    | C::Bitvector32SignedMultiplyOverflows(..)
                    | C::Bitvector32SignedDivideOverflows(..)
                    | C::Bitvector64SignedAddOverflows(..)
                    | C::Bitvector64SignedSubtractOverflows(..)
                    | C::Bitvector64SignedMultiplyOverflows(..)
                    | C::Bitvector64SignedDivideOverflows(..)
            )
            .then_some(false);
        }
        let overflow = match condition {
            C::Bitvector32SignedAddOverflows(a, b) => Some((Domain::Int32, a, b, Operation::Add)),
            C::Bitvector32SignedSubtractOverflows(a, b) => {
                Some((Domain::Int32, a, b, Operation::Subtract))
            }
            C::Bitvector32SignedMultiplyOverflows(a, b) => {
                Some((Domain::Int32, a, b, Operation::Multiply))
            }
            C::Bitvector64SignedAddOverflows(a, b) => Some((Domain::Int64, a, b, Operation::Add)),
            C::Bitvector64SignedSubtractOverflows(a, b) => {
                Some((Domain::Int64, a, b, Operation::Subtract))
            }
            C::Bitvector64SignedMultiplyOverflows(a, b) => {
                Some((Domain::Int64, a, b, Operation::Multiply))
            }
            _ => None,
        };
        if let Some((operation, domain, a, b, commutative)) = overflow_parts(condition)
            && let (Some(a), Some(b)) = (self.resolve(domain, a), self.resolve(domain, b))
            && self
                .no_overflow
                .contains(&overflow_key(operation, a, b, commutative))
        {
            return Some(false);
        }
        if let Some((domain, a, b, operation)) = overflow {
            return self.decide_overflow(domain, a, b, operation);
        }
        if let C::Bitvector32SignedShiftLeftOverflows(a, count) = condition {
            // As the general decision reads it: a shift by a constant count
            // does not overflow a value in `[0, INT_MAX >> count]`.
            let count = constant(Domain::Int32, count)?;
            if !(0..32).contains(&count) {
                return None;
            }
            let (low, high) = self.term_interval(Domain::Int32, a);
            return (low >= 0 && high <= i128::from(i32::MAX >> count)).then_some(false);
        }
        if let C::Bitvector32SignedDivideOverflows(a, b)
        | C::Bitvector64SignedDivideOverflows(a, b) = condition
        {
            // `a / b` overflows when `a` is the domain's least value and `b`
            // is `-1`. The `int64` condition also holds for a zero divisor
            // (`ConditionTerm::int64_signed_divide_overflows`); the `int32`
            // one leaves zero to a separate check. As above, only the
            // absence is answered.
            let int64 = matches!(condition, C::Bitvector64SignedDivideOverflows(..));
            let domain = if int64 { Domain::Int64 } else { Domain::Int32 };
            let (a_low, _) = self.term_interval(domain, a);
            let (b_low, b_high) = self.term_interval(domain, b);
            let excludes = |value: i128| {
                matches!(
                    self.resolve(domain, b),
                    Some((Some(node), offset)) if self.excludes(node, value - offset)
                )
            };
            let no_pair = a_low > domain.range().0 || b_low > -1 || b_high < -1 || excludes(-1);
            let nonzero = b_low > 0 || b_high < 0 || excludes(0);
            return (no_pair && (!int64 || nonzero)).then_some(false);
        }
        if let C::Bitvector32Equal(a, b) | C::Bitvector64Equal(a, b) = condition {
            let domains: &[Domain] = if matches!(condition, C::Bitvector32Equal(..)) {
                &[Domain::Int32]
            } else {
                &[Domain::Int64, Domain::UInt64]
            };
            for domain in domains {
                if let (Some(a), Some(b)) = (self.resolve(*domain, a), self.resolve(*domain, b)) {
                    match (a, b) {
                        ((Some(node), offset), (None, value))
                        | ((None, value), (Some(node), offset))
                            if self.excludes(node, value - offset) =>
                        {
                            return Some(false);
                        }
                        _ => {}
                    }
                    let ab = self.difference_bound(a, b);
                    let ba = self.difference_bound(b, a);
                    if ab <= 0 && ba <= 0 {
                        return Some(true);
                    }
                    if ab < 0 || ba < 0 {
                        return Some(false);
                    }
                }
                // A side the graph has no node for is compared by interval.
                let (a_low, a_high) = self.term_interval(*domain, a);
                let (b_low, b_high) = self.term_interval(*domain, b);
                if a_low == a_high && (a_low, a_high) == (b_low, b_high) {
                    return Some(true);
                }
                if a_high < b_low || b_high < a_low {
                    return Some(false);
                }
            }
            return None;
        }
        let [(domain, ref lower, ref upper, strict)] = condition_orders(condition, true)[..] else {
            return None;
        };
        // An unsigned `a - b` with `b <= a` does not wrap, so it lies in
        // `[0, a]`: it is at most `a`, and below `a` when `b >= 1`.
        if let (Domain::UInt64, Bitvector32Term::UInt64Subtract(a, b)) = (domain, lower)
            && a.as_ref() == upper
            && let (Some(a), Some(b)) = (self.resolve(domain, a), self.resolve(domain, b))
            && self.difference_bound(a, b) <= 0
            && (!strict || self.affine_interval(b).0 >= 1)
        {
            return Some(true);
        }
        // lower < upper (or <=) holds when lower - upper <= -strict, and
        // fails when upper - lower <= -(not strict).
        let (holds, fails) = match (self.resolve(domain, lower), self.resolve(domain, upper)) {
            (Some(lower), Some(upper)) => (
                self.difference_bound(upper, lower),
                self.difference_bound(lower, upper),
            ),
            // A side the graph has no node for is compared by interval.
            _ => {
                let (lower_low, lower_high) = self.term_interval(domain, lower);
                let (upper_low, upper_high) = self.term_interval(domain, upper);
                (lower_high - upper_low, upper_high - lower_low)
            }
        };
        if holds <= -i128::from(strict) {
            return Some(true);
        }
        if fails <= -i128::from(!strict) {
            return Some(false);
        }
        None
    }

    /// An interval holding `term`'s value in `domain`: a resolved term's
    /// stored bounds, narrowed for a sum or difference by the exact interval
    /// of its operands' mathematical result when that stays in `domain` (so
    /// the bitvector operation does not wrap). Anything else ranges over
    /// `domain`. Work is the term's size, plus the difference reads of
    /// `difference_interval`.
    fn term_interval(&self, domain: Domain, term: &Bitvector32Term) -> (i128, i128) {
        // A compound term a fact mentioned has a node of its own, whose
        // interval holds only what facts about the term said; its operands'
        // intervals may say more, so both are read.
        let (node_low, node_high) = self
            .resolve(domain, term)
            .map_or_else(|| domain.range(), |affine| self.affine_interval(affine));
        let (low, high) = self.structural_interval(domain, term);
        (node_low.max(low), node_high.min(high))
    }

    /// `term_interval` from `term`'s operands alone.
    fn structural_interval(&self, domain: Domain, term: &Bitvector32Term) -> (i128, i128) {
        use Bitvector32Term as T;
        if matches!(term, T::Variable(_) | T::Constant(_)) {
            // No operands to read: nothing to charge.
            return domain.range();
        }
        charge();
        let (low, high) = match (domain, term) {
            (Domain::Int32, T::Add(a, b))
            | (Domain::Int64, T::Int64Add(a, b))
            | (Domain::UInt64, T::UInt64Add(a, b)) => {
                let (a_low, a_high) = self.term_interval(domain, a);
                let (b_low, b_high) = self.term_interval(domain, b);
                (a_low + b_low, a_high + b_high)
            }
            (Domain::Int32, T::Subtract(a, b))
            | (Domain::Int64, T::Int64Subtract(a, b))
            | (Domain::UInt64, T::UInt64Subtract(a, b)) => self.difference_interval(domain, a, b),
            (Domain::Int32, T::Multiply(a, b)) | (Domain::Int64, T::Int64Multiply(a, b)) => {
                let (a_low, a_high) = self.term_interval(domain, a);
                let (b_low, b_high) = self.term_interval(domain, b);
                let products = [
                    a_low * b_low,
                    a_low * b_high,
                    a_high * b_low,
                    a_high * b_high,
                ];
                let low = products.iter().min().copied().unwrap_or(i128::MIN);
                let high = products.iter().max().copied().unwrap_or(i128::MAX);
                (low, high)
            }
            // C's truncating remainder by a constant other than 0 and -1:
            // its sign is the dividend's, and its magnitude is below the
            // divisor's and at most the dividend's.
            (Domain::Int32, T::Remainder(a, b))
                if constant(domain, b).is_some_and(|k| k != 0 && k != -1) =>
            {
                let k = constant(domain, b).expect("checked above");
                let (a_low, a_high) = self.term_interval(domain, a);
                let bound = k.abs() - 1;
                if a_low == a_high {
                    (a_low % k, a_low % k)
                } else if a_low >= 0 {
                    (0, a_high.min(bound))
                } else if a_high <= 0 {
                    (a_low.max(-bound), 0)
                } else {
                    (-bound, bound)
                }
            }
            (Domain::Int64, T::Int64From32(inner)) => self.term_interval(Domain::Int32, inner),
            // Unsigned division by a divisor known to be positive.
            (Domain::UInt64, T::UInt64Divide(a, b)) => {
                let (a_low, a_high) = self.term_interval(domain, a);
                let (b_low, b_high) = self.term_interval(domain, b);
                if b_low < 1 {
                    return domain.range();
                }
                (a_low / b_high, a_high / b_low)
            }
            // Zero extension: a non-negative `int32` keeps its value, a
            // negative one gains 2^32, and an operand of unknown sign lands
            // in `[0, 2^32)`.
            (Domain::Int64, T::Int64FromUInt32(inner)) => {
                let (low, high) = self.term_interval(Domain::Int32, inner);
                if low >= 0 {
                    (low, high)
                } else if high < 0 {
                    (low + (1 << 32), high + (1 << 32))
                } else {
                    (0, (1 << 32) - 1)
                }
            }
            _ => return domain.range(),
        };
        let (min, max) = domain.range();
        if low >= min && high <= max {
            (low, high)
        } else {
            (min, max)
        }
    }

    /// The mathematical interval of `a - b` in `domain`: the operands'
    /// intervals, narrowed by the graph's bound on their difference when
    /// both resolve to nodes.
    fn difference_interval(
        &self,
        domain: Domain,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
    ) -> (i128, i128) {
        let (a_low, a_high) = self.term_interval(domain, a);
        let (b_low, b_high) = self.term_interval(domain, b);
        let mut high = a_high - b_low;
        let mut low = a_low - b_high;
        if let (Some(a), Some(b)) = (self.resolve(domain, a), self.resolve(domain, b)) {
            high = high.min(self.difference_bound(b, a));
            low = low.max(-self.difference_bound(a, b));
        }
        (low, high)
    }

    /// Whether `a op b` leaves `domain`, from the operands' intervals and,
    /// for a subtraction of two nodes, the difference between them. An
    /// operand the graph cannot resolve ranges over its domain.
    fn decide_overflow(
        &self,
        domain: Domain,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        operation: Operation,
    ) -> Option<bool> {
        let (a_low, a_high) = self.term_interval(domain, a);
        let (b_low, b_high) = self.term_interval(domain, b);
        let (low, high) = match operation {
            Operation::Add => (a_low + b_low, a_high + b_high),
            Operation::Subtract => self.difference_interval(domain, a, b),
            Operation::Multiply => {
                let products = [
                    a_low * b_low,
                    a_low * b_high,
                    a_high * b_low,
                    a_high * b_high,
                ];
                (*products.iter().min()?, *products.iter().max()?)
            }
        };
        let (min, max) = domain.range();
        // Only the absence of overflow is answered. Proof terms that are
        // not C (an arithmetic certificate's intermediate sums) are lowered
        // through the C evaluator and read an undecided overflow as a value;
        // see `issues/difference-logic.md`.
        (low >= min && high <= max).then_some(false)
    }
}

/// A fact context's graph: extended as the context assumes condition
/// facts, cleared when it withdraws one (a graph cannot drop an edge), and
/// rebuilt from the context's facts by the next query that finds it
/// cleared. Clones share it, as proof branches share the context.
#[derive(Clone)]
pub(crate) struct ContextDifferenceGraph(std::sync::Arc<std::sync::OnceLock<DifferenceGraph>>);

impl Default for ContextDifferenceGraph {
    fn default() -> Self {
        Self(std::sync::Arc::new(std::sync::OnceLock::from(
            DifferenceGraph::new(),
        )))
    }
}

impl std::fmt::Debug for ContextDifferenceGraph {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("ContextDifferenceGraph")
    }
}

impl ContextDifferenceGraph {
    /// Follows the context assuming `condition` with `value`; a cleared
    /// graph stays cleared until its rebuild.
    pub(crate) fn assume(&mut self, condition: &ConditionTerm, value: bool) {
        if !expresses(condition) {
            return;
        }
        if let Some(graph) = self.0.get() {
            let mut graph = graph.clone();
            graph.assume_condition(condition, value);
            self.0 = std::sync::Arc::new(std::sync::OnceLock::from(graph));
        }
    }

    /// Follows the context withdrawing `condition`.
    pub(crate) fn withdraw(&mut self, condition: &ConditionTerm) {
        if expresses(condition) {
            self.0 = std::sync::Arc::new(std::sync::OnceLock::new());
        }
    }

    /// Restarts from no facts, for a context about to re-assume all of its
    /// facts.
    pub(crate) fn reset(&mut self) {
        *self = Self::default();
    }

    /// The graph, unless it was cleared and not yet rebuilt.
    pub(crate) fn built(&self) -> Option<&DifferenceGraph> {
        self.0.get()
    }

    /// The graph of the context's `facts`, rebuilt from them when cleared.
    pub(crate) fn graph<'a>(
        &self,
        facts: impl FnOnce() -> Vec<(&'a ConditionTerm, bool)>,
    ) -> &DifferenceGraph {
        self.0.get_or_init(|| {
            let mut graph = DifferenceGraph::new();
            for (condition, value) in facts() {
                graph.assume_condition(condition, value);
            }
            graph
        })
    }
}

/// Whether difference logic reads anything from a fact about `condition`.
fn expresses(condition: &ConditionTerm) -> bool {
    use ConditionTerm as C;
    matches!(condition, C::PointerEqual(..))
        || overflow_parts(condition).is_some()
        || offset_equality(condition).is_some()
        || matches!(
            condition,
            C::Bitvector32SignedLessThan(..)
                | C::Bitvector32SignedLessEqual(..)
                | C::Bitvector32SignedGreaterThan(..)
                | C::Bitvector32SignedGreaterEqual(..)
                | C::Bitvector32Equal(..)
                | C::Bitvector64SignedLessThan(..)
                | C::Bitvector64SignedLessEqual(..)
                | C::Bitvector64SignedGreaterThan(..)
                | C::Bitvector64SignedGreaterEqual(..)
                | C::Bitvector64UnsignedLessThan(..)
                | C::Bitvector64UnsignedLessEqual(..)
                | C::Bitvector64UnsignedGreaterThan(..)
                | C::Bitvector64UnsignedGreaterEqual(..)
                | C::Bitvector64Equal(..)
        )
}

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Subtract,
    Multiply,
}

/// The parts of an overflow condition: its operation, the operands'
/// domain, the operands, and whether the operation is commutative.
fn overflow_parts(
    condition: &ConditionTerm,
) -> Option<(u8, Domain, &Bitvector32Term, &Bitvector32Term, bool)> {
    use ConditionTerm as C;
    Some(match condition {
        C::Bitvector32SignedAddOverflows(a, b) => (0, Domain::Int32, a, b, true),
        C::Bitvector32SignedSubtractOverflows(a, b) => (1, Domain::Int32, a, b, false),
        C::Bitvector32SignedMultiplyOverflows(a, b) => (2, Domain::Int32, a, b, true),
        C::Bitvector32SignedDivideOverflows(a, b) => (3, Domain::Int32, a, b, false),
        C::Bitvector32SignedShiftLeftOverflows(a, b) => (4, Domain::Int32, a, b, false),
        C::Bitvector64SignedAddOverflows(a, b) => (5, Domain::Int64, a, b, true),
        C::Bitvector64SignedSubtractOverflows(a, b) => (6, Domain::Int64, a, b, false),
        C::Bitvector64SignedMultiplyOverflows(a, b) => (7, Domain::Int64, a, b, true),
        C::Bitvector64SignedDivideOverflows(a, b) => (8, Domain::Int64, a, b, false),
        _ => return None,
    })
}

/// A recorded overflow condition: its operation and its operands' values
/// in the graph, a commutative operation's in one order, so another name
/// for an operand, or the operands swapped, finds it.
type OverflowKey = (u8, Affine, Affine);

fn overflow_key(operation: u8, a: Affine, b: Affine, commutative: bool) -> OverflowKey {
    if commutative && b < a {
        (operation, b, a)
    } else {
        (operation, a, b)
    }
}

/// Whether a value in `(low, high)` plus `offset` stays in `domain` (and,
/// for a conversion that keeps only non-negative values, is non-negative).
fn link_fits((low, high): (i128, i128), offset: i128, domain: Domain, nonnegative: bool) -> bool {
    let (min, max) = domain.range();
    if nonnegative {
        low >= 0 && high <= max
    } else {
        low + offset >= min && high + offset <= max
    }
}

/// A cast between integer types held as `int32` values: its operand, the
/// source type's range, and the modulus of the destination's width.
#[derive(Clone, Copy, Debug)]
struct CastLink {
    base: NodeId,
    source: (i128, i128),
    modulus: i128,
}

/// The range of a narrow integer type as its `int32` value holds it.
fn narrow_range(kind: crate::kernel::MachineIntegerType) -> Option<(i128, i128)> {
    use crate::kernel::MachineIntegerType as M;
    Some(match kind {
        M::Int8 => (-128, 127),
        M::UInt8 => (0, 255),
        M::Int16 => (-32_768, 32_767),
        M::UInt16 => (0, 65_535),
        M::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
        _ => return None,
    })
}

/// A cast between narrow integer types (`int32` or narrower, as `int32`
/// values): its operand, the source and destination ranges, and the
/// destination's modulus. The cast keeps the operand modulo that modulus.
fn narrow_cast_parts(
    domain: Domain,
    term: &Bitvector32Term,
) -> Option<(&Bitvector32Term, (i128, i128), (i128, i128), i128)> {
    let (
        Domain::Int32,
        Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        },
    ) = (domain, term)
    else {
        return None;
    };
    let source_range = narrow_range(*source)?;
    let destination_range = narrow_range(*destination)?;
    let modulus = destination_range.1 - destination_range.0 + 1;
    Some((value, source_range, destination_range, modulus))
}

/// When `term` is `x ^ MIN` in a signed `domain`, the spelling of an
/// unsigned order as a signed one: `x`.
fn sign_flip_base(domain: Domain, term: &Bitvector32Term) -> Option<&Bitvector32Term> {
    use Bitvector32Term as T;
    let (a, b) = match (domain, term) {
        (Domain::Int32, T::BitwiseXor(a, b)) | (Domain::Int64, T::Int64BitwiseXor(a, b)) => {
            (a.as_ref(), b.as_ref())
        }
        _ => return None,
    };
    let min = Some(domain.range().0);
    if constant(domain, a) == min {
        Some(b)
    } else if constant(domain, b) == min {
        Some(a)
    } else {
        None
    }
}

/// `value ^ MIN` in a signed `domain`.
fn flip_sign(domain: Domain, value: i128) -> i128 {
    let min = domain.range().0;
    if value >= 0 { value + min } else { value - min }
}

/// A pointer offset as `value * width` for an `int32` value, or a constant
/// byte offset. Exact: the product is formed in 64 bits.
enum ScaledOffset<'a> {
    Scaled(&'a Bitvector32Term, i64),
    Bytes(i64),
}

fn scaled_offset(offset: &crate::kernel::PointerOffsetTerm) -> Option<ScaledOffset<'_>> {
    use crate::kernel::PointerOffsetTerm as O;
    match offset {
        O::Int32Scaled { value, byte_width } if *byte_width != 0 => {
            Some(ScaledOffset::Scaled(value, *byte_width))
        }
        O::Constant(bytes) => Some(ScaledOffset::Bytes(*bytes)),
        _ => None,
    }
}

/// `a == b` for two pointer offsets as an `int32` equality: equal widths
/// compare their values, and a constant byte offset that is a whole
/// number of elements compares the value with that count.
fn offset_equality(condition: &ConditionTerm) -> Option<ConditionTerm> {
    let ConditionTerm::PointerOffsetEqual(a, b) = condition else {
        return None;
    };
    let (a, b) = match (scaled_offset(a)?, scaled_offset(b)?) {
        (ScaledOffset::Scaled(a, wa), ScaledOffset::Scaled(b, wb)) if wa == wb => {
            (a.clone(), b.clone())
        }
        (ScaledOffset::Scaled(value, width), ScaledOffset::Bytes(bytes))
        | (ScaledOffset::Bytes(bytes), ScaledOffset::Scaled(value, width))
            if bytes % width == 0 =>
        {
            let count = i32::try_from(bytes / width).ok()?;
            (value.clone(), Bitvector32Term::Constant(count as u32))
        }
        _ => return None,
    };
    Some(ConditionTerm::Bitvector32Equal(Box::new(a), Box::new(b)))
}

/// Two pointer offsets that cannot be equal whatever their values: a
/// constant byte offset that no whole number of `int32` elements reaches.
fn offset_mismatch(
    a: &crate::kernel::PointerOffsetTerm,
    b: &crate::kernel::PointerOffsetTerm,
) -> Option<bool> {
    match (scaled_offset(a)?, scaled_offset(b)?) {
        (ScaledOffset::Scaled(_, width), ScaledOffset::Bytes(bytes))
        | (ScaledOffset::Bytes(bytes), ScaledOffset::Scaled(_, width)) => {
            let count = bytes / width;
            (bytes % width != 0 || i32::try_from(count).is_err()).then_some(false)
        }
        _ => None,
    }
}

/// Equality and disequality between pointer terms, as a union-find with
/// union by size (so a find walks at most a logarithmic chain) and, per
/// class root, the pointers known unequal to the class. A union merges the
/// smaller class's disequalities into the larger's.
#[derive(Clone, Debug, Default)]
struct PointerClasses {
    ids: PersistentMap<Pointer, NodeId>,
    terms: PersistentMap<NodeId, Pointer>,
    /// The ids of the pointers with each offset, for an offset question.
    by_offset: PersistentMap<PointerOffsetTerm, crate::persistent::PersistentSet<NodeId>>,
    parent: PersistentMap<NodeId, NodeId>,
    size: PersistentMap<NodeId, usize>,
    unequal: PersistentMap<NodeId, crate::persistent::PersistentSet<NodeId>>,
    next: NodeId,
}

impl PointerClasses {
    fn id(&mut self, pointer: &Pointer) -> NodeId {
        if let Some(id) = self.ids.get(pointer) {
            return *id;
        }
        charge();
        let id = self.next;
        self.next += 1;
        self.ids.insert(pointer.clone(), id);
        self.terms.insert(id, pointer.clone());
        let mut same_offset = self
            .by_offset
            .get(&pointer.offset)
            .cloned()
            .unwrap_or_default();
        same_offset = same_offset.with_value(id);
        self.by_offset.insert(pointer.offset.clone(), same_offset);
        id
    }

    fn find(&self, mut id: NodeId) -> NodeId {
        while let Some(parent) = self.parent.get(&id) {
            charge();
            id = *parent;
        }
        id
    }

    /// Whether two class roots are known unequal, from the smaller of their
    /// disequality sets. Past `EDGE_LIMIT` entries it answers no, which
    /// only answers less.
    fn roots_unequal(&self, a: NodeId, b: NodeId) -> bool {
        let empty = crate::persistent::PersistentSet::default();
        let (a_set, b_set) = (
            self.unequal.get(&a).unwrap_or(&empty),
            self.unequal.get(&b).unwrap_or(&empty),
        );
        let (set, other) = if a_set.len() <= b_set.len() {
            (a_set, b)
        } else {
            (b_set, a)
        };
        set.iter().take(EDGE_LIMIT).any(|id| {
            charge();
            self.find(*id) == other
        })
    }

    /// Records `a == b` (`value`) or `a != b`; false when that contradicts
    /// what is recorded.
    fn assume(&mut self, a: &Pointer, b: &Pointer, value: bool) -> bool {
        let (a, b) = (self.id(a), self.id(b));
        let (root_a, root_b) = (self.find(a), self.find(b));
        if !value {
            if root_a == root_b {
                return false;
            }
            for (root, other) in [(root_a, b), (root_b, a)] {
                let set = self.unequal.get(&root).cloned().unwrap_or_default();
                self.unequal.insert(root, set.with_value(other));
            }
            return true;
        }
        if root_a == root_b {
            return true;
        }
        if self.roots_unequal(root_a, root_b) {
            return false;
        }
        let size = |root| self.size.get(&root).copied().unwrap_or(1);
        let (small, large) = if size(root_a) <= size(root_b) {
            (root_a, root_b)
        } else {
            (root_b, root_a)
        };
        let merged = size(small) + size(large);
        self.parent.insert(small, large);
        self.size.insert(large, merged);
        if let Some(moved) = self.unequal.get(&small).cloned() {
            let mut set = self.unequal.get(&large).cloned().unwrap_or_default();
            for id in moved.iter() {
                charge();
                set = set.with_value(*id);
            }
            self.unequal.insert(large, set);
            self.unequal.remove(&small);
        }
        true
    }

    fn decide(&self, a: &Pointer, b: &Pointer) -> Option<bool> {
        let (a, b) = (self.ids.get(a)?, self.ids.get(b)?);
        let (root_a, root_b) = (self.find(*a), self.find(*b));
        if root_a == root_b {
            Some(true)
        } else {
            self.roots_unequal(root_a, root_b).then_some(false)
        }
    }

    /// `a == b` for two offsets of one block, read from recorded pointers
    /// in a common block with those offsets: such pointers are equal
    /// exactly when their offsets are.
    fn decide_offsets(&self, a: &PointerOffsetTerm, b: &PointerOffsetTerm) -> Option<bool> {
        let (with_a, with_b) = (self.by_offset.get(a)?, self.by_offset.get(b)?);
        let pairs = with_a
            .iter()
            .flat_map(|left| with_b.iter().map(move |right| (left, right)));
        for (left, right) in pairs.take(EDGE_LIMIT) {
            charge();
            let (left, right) = (self.terms.get(left)?, self.terms.get(right)?);
            if left.block != right.block {
                continue;
            }
            if let Some(answer) = self.decide(left, right) {
                return Some(answer);
            }
        }
        None
    }
}

/// `term`'s value in `domain` when it is a constant there.
fn constant(domain: Domain, term: &Bitvector32Term) -> Option<i128> {
    use Bitvector32Term as T;
    match (domain, term) {
        (Domain::Int32, T::Constant(value)) => Some(i128::from(*value as i32)),
        (Domain::Int64, T::Int64Constant(value)) => Some(i128::from(*value)),
        (Domain::UInt64, T::UInt64Constant(value)) => Some(i128::from(*value)),
        (Domain::UInt64, T::Int64Constant(value)) if *value >= 0 => Some(i128::from(*value)),
        _ => None,
    }
}

/// When `term` is a base plus a constant in `domain`, or a conversion that
/// keeps its operand's value: the base's domain, the base, the constant,
/// and whether only a non-negative base keeps its value.
fn link_parts(
    domain: Domain,
    term: &Bitvector32Term,
) -> Option<(Domain, &Bitvector32Term, i128, bool)> {
    use Bitvector32Term as T;
    match (domain, term) {
        (Domain::Int32, T::Add(left, right))
        | (Domain::Int64, T::Int64Add(left, right))
        | (Domain::UInt64, T::UInt64Add(left, right)) => {
            if let Some(k) = constant(domain, right) {
                Some((domain, left, k, false))
            } else {
                constant(domain, left).map(|k| (domain, right.as_ref(), k, false))
            }
        }
        (Domain::Int32, T::Subtract(left, right))
        | (Domain::Int64, T::Int64Subtract(left, right))
        | (Domain::UInt64, T::UInt64Subtract(left, right)) => {
            constant(domain, right).map(|k| (domain, left.as_ref(), -k, false))
        }
        // Sign extension keeps every value.
        (Domain::Int64, T::Int64From32(inner)) => Some((Domain::Int32, inner, 0, false)),
        // Reinterpreting as unsigned keeps a non-negative value.
        (Domain::UInt64, T::UInt64From32(inner)) => Some((Domain::Int32, inner, 0, true)),
        (Domain::UInt64, T::UInt64FromInt64(inner)) => Some((Domain::Int64, inner, 0, true)),
        // Zero extension of an `int32` bit pattern keeps a non-negative
        // value; so does sign extension read as unsigned.
        (Domain::Int64, T::Int64FromUInt32(inner))
        | (Domain::UInt64, T::UInt64FromInt32(inner)) => Some((Domain::Int32, inner, 0, true)),
        _ => None,
    }
}

/// The orders a condition with `value` states, as
/// `(domain, lower, upper, strict)` for `lower < upper` or `lower <= upper`;
/// a true equality is two. Empty for a fact difference logic does not
/// express.
fn condition_orders(
    condition: &ConditionTerm,
    value: bool,
) -> Vec<(Domain, Bitvector32Term, Bitvector32Term, bool)> {
    use ConditionTerm as C;
    let (domain, left, right, strict) = match condition {
        C::Bitvector32SignedLessThan(a, b) => (Domain::Int32, a, b, true),
        C::Bitvector32SignedLessEqual(a, b) => (Domain::Int32, a, b, false),
        C::Bitvector32SignedGreaterThan(a, b) => (Domain::Int32, b, a, true),
        C::Bitvector32SignedGreaterEqual(a, b) => (Domain::Int32, b, a, false),
        C::Bitvector64SignedLessThan(a, b) => (Domain::Int64, a, b, true),
        C::Bitvector64SignedLessEqual(a, b) => (Domain::Int64, a, b, false),
        C::Bitvector64SignedGreaterThan(a, b) => (Domain::Int64, b, a, true),
        C::Bitvector64SignedGreaterEqual(a, b) => (Domain::Int64, b, a, false),
        C::Bitvector64UnsignedLessThan(a, b) => (Domain::UInt64, a, b, true),
        C::Bitvector64UnsignedLessEqual(a, b) => (Domain::UInt64, a, b, false),
        C::Bitvector64UnsignedGreaterThan(a, b) => (Domain::UInt64, b, a, true),
        C::Bitvector64UnsignedGreaterEqual(a, b) => (Domain::UInt64, b, a, false),
        C::Bitvector32Equal(a, b) | C::Bitvector64Equal(a, b) if value => {
            let domains: &[Domain] = if matches!(condition, C::Bitvector32Equal(..)) {
                &[Domain::Int32]
            } else {
                &[Domain::Int64, Domain::UInt64]
            };
            let (a, b) = (a.as_ref(), b.as_ref());
            return domains
                .iter()
                .flat_map(|domain| {
                    [
                        (*domain, a.clone(), b.clone(), false),
                        (*domain, b.clone(), a.clone(), false),
                    ]
                })
                .collect();
        }
        _ => return Vec::new(),
    };
    let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
    if value {
        vec![(domain, left, right, strict)]
    } else {
        // not (l < r) is r <= l; not (l <= r) is r < l.
        vec![(domain, right, left, !strict)]
    }
}

#[cfg(test)]
#[path = "difference_graph/tests.rs"]
pub(crate) mod tests;
