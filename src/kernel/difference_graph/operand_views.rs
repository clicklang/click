//! Borrowed arithmetic queries over the existing difference graph.
use super::*;
pub(super) mod cache;
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
use crate::kernel::uint64_constant;
use crate::kernel::{MachineCastSpelling as E, MachineOperandView as V};
use cache::{Answer, Kind, QueryKey, Read};

pub(super) fn format(domain: Domain) -> MachineIntegerType {
    match domain {
        Domain::Int32 => MachineIntegerType::Int32,
        Domain::UInt32 => MachineIntegerType::UInt32,
        Domain::Int64 => MachineIntegerType::Int64,
        Domain::UInt64 => MachineIntegerType::UInt64,
        Domain::Narrow(ty) => ty,
    }
}

fn atom(term: V<'_>) -> Option<MachineTerm> {
    term.literal()
        .or_else(|| term.variable().copied().map(MachineTerm::Variable))
}
pub(super) fn constant_view(domain: Domain, term: V<'_>) -> Option<i128> {
    constant(domain, &term.literal()?)
}
fn binary_domain(domain: Domain, ty: MachineIntegerType) -> bool {
    match domain {
        Domain::Int32 => matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32),
        Domain::Int64 => ty == MachineIntegerType::Int64,
        Domain::UInt64 => ty == MachineIntegerType::UInt64,
        _ => false,
    }
}
fn modular_parts_view(domain: Domain, term: V<'_>) -> Option<(V<'_>, i128)> {
    let (ty, op, [a, b]) = term.binary()?;
    if !binary_domain(domain, ty) {
        return None;
    }
    match op {
        MachineBinaryOp::Add => constant_view(domain, b)
            .map(|k| (a, k))
            .or_else(|| constant_view(domain, a).map(|k| (b, k))),
        MachineBinaryOp::Subtract => constant_view(domain, b).map(|k| (a, -k)),
        _ => None,
    }
}
pub(super) fn link_parts_view(domain: Domain, term: V<'_>) -> Option<(Domain, V<'_>, i128, bool)> {
    if let Some((base, k)) = modular_parts_view(domain, term) {
        return Some((domain, base, k, false));
    }
    let (encoding, source, destination, base) = term.cast()?;
    match (domain, encoding) {
        (Domain::Int32 | Domain::UInt32, E::Generic)
            if crate::kernel::is_narrow_widening32(source, destination) =>
        {
            Some((Domain::Narrow(source), base, 0, false))
        }
        (Domain::Int32 | Domain::UInt32, E::Generic)
            if crate::kernel::is_sign_cast32(source, destination) =>
        {
            Some((domain, base, 0, false))
        }
        (Domain::Int64, E::Int64From32) => Some((Domain::Int32, base, 0, false)),
        (Domain::UInt64, E::UInt64From32) => Some((Domain::UInt32, base, 0, false)),
        (Domain::UInt64, E::UInt64FromInt64) => Some((Domain::Int64, base, 0, true)),
        (Domain::Int64, E::Int64FromUInt32) | (Domain::UInt64, E::UInt64FromInt32) => {
            Some((Domain::Int32, base, 0, true))
        }
        _ => None,
    }
}
pub(super) fn sign_flip_view(domain: Domain, term: V<'_>) -> Option<V<'_>> {
    let (ty, MachineBinaryOp::BitwiseXor, [a, b]) = term.binary()? else {
        return None;
    };
    if !matches!(domain, Domain::Int32 | Domain::Int64) || !binary_domain(domain, ty) {
        return None;
    }
    let min = domain.range().0;
    if constant_view(domain, b) == Some(min) {
        Some(a)
    } else if constant_view(domain, a) == Some(min) {
        Some(b)
    } else {
        None
    }
}

pub(super) fn narrow_cast_view(
    domain: Domain,
    term: V<'_>,
) -> Option<(V<'_>, (i128, i128), (i128, i128), i128)> {
    let (E::Generic, source, destination, value) = term.cast()? else {
        return None;
    };
    if domain != Domain::Int32 {
        return None;
    }
    let source = narrow_range(source)?;
    let destination = narrow_range(destination)?;
    Some((
        value,
        source,
        destination,
        destination.1 - destination.0 + 1,
    ))
}

pub(super) fn word_mask_view(term: V<'_>) -> Option<(i128, V<'_>)> {
    let (ty, MachineBinaryOp::BitwiseAnd, [a, b]) = term.binary()? else {
        return None;
    };
    if !binary_domain(Domain::Int32, ty) {
        return None;
    }
    constant_view(Domain::UInt32, b)
        .map(|mask| (mask, a))
        .or_else(|| constant_view(Domain::UInt32, a).map(|mask| (mask, b)))
}

struct Query<'a> {
    graph: &'a DifferenceGraph,
    frames: Vec<(Vec<Read>, bool)>,
}

impl DifferenceGraph {
    pub(super) fn index_operand_node(&mut self, domain: Domain, term: &MachineTerm, node: NodeId) {
        let named_read = matches!(term, MachineTerm::Variable(variable)
            if crate::kernel::is_load_variable(variable));
        if !named_read && matches!(term, MachineTerm::Variable(_))
            || V::Legacy(term).literal().is_some()
        {
            self.shared_queries.invalidate(Read::Operand(
                domain,
                Key::for_format(format(domain), V::Legacy(term)),
            ));
            return;
        }
        // Index only arithmetic admitted by a written fact. Opaque legacy
        // payloads stay in the original table and are never imported here.
        let interpretation = format(domain);
        let alternate = match domain {
            Domain::Int32 => Some(MachineIntegerType::UInt32),
            Domain::UInt32 => Some(MachineIntegerType::Int32),
            Domain::Int64 => Some(MachineIntegerType::UInt64),
            Domain::UInt64 => Some(MachineIntegerType::Int64),
            Domain::Narrow(_) => None,
        };
        let retained = crate::kernel::SharedMachineIntegerTerm::retained_import(
            interpretation,
            term,
        )
        .or_else(|| {
            alternate
                .and_then(|ty| crate::kernel::SharedMachineIntegerTerm::retained_import(ty, term))
        });
        let root = retained
            .as_ref()
            .and_then(|value| value.shared_operand())
            .map(|root| root.with_machine_observation_type(interpretation))
            .or_else(|| {
                crate::kernel::KernelTermImport::default().machine_arithmetic(interpretation, term)
            });
        if let Some(root) = root {
            // A compatibility name can introduce a read before any shared
            // comparison does. Index its descriptor at the same coordinate,
            // so structural address indices use the already-admitted bounds.
            self.has_shared_admissions |= root.has_machine_reads();
            let key = Key::for_format(format(domain), V::Shared(&root));
            self.shared_queries
                .invalidate(Read::Operand(domain, key.clone()));
            self.operand_affines.insert((domain, key), (Some(node), 0));
        }
    }

    pub(super) fn invalidate_operand(&mut self, domain: Domain, term: V<'_>) {
        self.shared_queries
            .invalidate(Read::Operand(domain, Key::for_format(format(domain), term)));
    }

    /// The existing order decision, with retained comparison operands.
    /// Word equality has the same truth in either signedness reading. Keep
    /// the native rule's exclusions, difference bounds and singleton ranges,
    /// but resolve selected shared operands without exporting their trees.
    pub(crate) fn decide_word_equality_views(&self, a: V<'_>, b: V<'_>) -> Option<bool> {
        self.decide_equality_views(MachineIntegerType::Int32, a, b)
    }

    pub(super) fn decide_equality_views(
        &self,
        format: MachineIntegerType,
        a: V<'_>,
        b: V<'_>,
    ) -> Option<bool> {
        if self.contradictory {
            return None;
        }
        if format.format().bits() == 64
            && let (V::Legacy(a), V::Legacy(b)) = (a, b)
        {
            return self.decide_native_wide_equality(a, b);
        }
        let mut query = Query::new(self);
        let domains = if format.format().bits() == 32 {
            [Domain::Int32, Domain::UInt32]
        } else {
            [Domain::Int64, Domain::UInt64]
        };
        for domain in domains {
            if let (Some(a), Some(b)) = (query.resolve(domain, a), query.resolve(domain, b)) {
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
            let (a_low, a_high) = query.interval(domain, a);
            let (b_low, b_high) = query.interval(domain, b);
            if a_low == a_high && (a_low, a_high) == (b_low, b_high) {
                return Some(true);
            }
            if a_high < b_low || b_high < a_low {
                return Some(false);
            }
        }
        if format.format().bits() == 64 {
            self.residues.decide_equal_views(a, b)
        } else {
            None
        }
    }

    /// Rounding down by a nonzero divisor preserves a non-strict upper bound.
    /// Follow only the supplied dividend chain. The operands remain borrowed
    /// views, and divisor queries use the graph's existing selected indexes.
    pub(super) fn decide_rounded_upper_bound(
        &self,
        lower: V<'_>,
        upper: V<'_>,
        strict: bool,
    ) -> Option<bool> {
        if strict {
            return None;
        }
        let (MachineIntegerType::UInt64, MachineBinaryOp::Subtract, [dividend, removed]) =
            lower.binary()?
        else {
            return None;
        };
        let key = |value| Key::for_format(MachineIntegerType::UInt64, value);
        if key(dividend) == key(upper) {
            return None; // The direct dividend bound is handled by the caller.
        }
        let (MachineIntegerType::UInt64, MachineBinaryOp::Remainder, [same_dividend, divisor]) =
            removed.binary()?
        else {
            return None;
        };
        if key(same_dividend) != key(dividend) || !Query::new(self).nonzero(Domain::UInt64, divisor)
        {
            return None;
        }
        let premise = crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::UInt64,
            crate::kernel::CompareRelation::LessEqual,
            [dividend, upper],
        );
        (self.decide(&premise) == Some(true)).then_some(true)
    }

    pub(crate) fn decide_shared_order(
        &self,
        view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::Relation;
        if self.contradictory {
            return None;
        }
        if let Some(widened) = view.widened() {
            return self.decide_shared_order(&widened);
        }
        let strict = match view.relation {
            Relation::Less => true,
            Relation::LessEqual => false,
            _ => return None,
        };
        let domain = match view.format {
            MachineIntegerType::Int32 => Domain::Int32,
            MachineIntegerType::UInt32 => Domain::UInt32,
            MachineIntegerType::Int64 => Domain::Int64,
            MachineIntegerType::UInt64 => Domain::UInt64,
            _ => return None,
        };
        let [lower, upper] = view.operands.each_ref().map(|p| p.operand_view());
        let mut query = Query::new(self);
        if domain == Domain::UInt64
            && let Some((MachineIntegerType::UInt64, op, [a, b])) = lower.binary()
            && Key::for_format(view.format, a) == Key::for_format(view.format, upper)
        {
            // `a - a % k` by a nonzero `k`: the remainder is at most `a`.
            if op == MachineBinaryOp::Subtract
                && !strict
                && let Some((MachineIntegerType::UInt64, MachineBinaryOp::Remainder, [x, k])) =
                    b.binary()
                && Key::for_format(view.format, x) == Key::for_format(view.format, a)
                && query.nonzero(domain, k)
            {
                return Some(true);
            }
            if op == MachineBinaryOp::Subtract
                && let (Some(a), Some(b)) = (query.resolve(domain, a), query.resolve(domain, b))
                && self.difference_bound(a, b) <= 0
                && (!strict || self.affine_interval(b).0 >= 1)
            {
                return Some(true);
            }
            // `a % 0` is an opaque value: only a nonzero divisor bounds it.
            if op == MachineBinaryOp::Remainder && !strict && query.nonzero(domain, b) {
                return Some(true);
            }
        }
        if domain == Domain::UInt64
            && let Some(value) = self.decide_rounded_upper_bound(lower, upper, strict)
        {
            return Some(value);
        }
        let (holds, fails) = match (query.resolve(domain, lower), query.resolve(domain, upper)) {
            (Some(lower), Some(upper)) => {
                if lower.0.is_some() && upper.0.is_some() {
                    if self
                        .direct_difference_bound(upper, lower)
                        .is_some_and(|bound| bound <= -i128::from(strict))
                    {
                        return Some(true);
                    }
                    if self
                        .direct_difference_bound(lower, upper)
                        .is_some_and(|bound| bound <= -i128::from(!strict))
                    {
                        return Some(false);
                    }
                }
                (
                    self.difference_bound(upper, lower),
                    self.difference_bound(lower, upper),
                )
            }
            _ => {
                let (l0, l1) = query.interval(domain, lower);
                let (u0, u1) = query.interval(domain, upper);
                (l1 - u0, u1 - l0)
            }
        };
        if holds <= -i128::from(strict) {
            Some(true)
        } else if fails <= -i128::from(!strict) {
            Some(false)
        } else {
            None
        }
    }

    pub(crate) fn decide_overflow_query(
        &self,
        query: &crate::kernel::machine_integer::definedness::OverflowQueryView,
    ) -> Option<bool> {
        use crate::kernel::machine_integer::Operation as Op;
        let domain = match query.format {
            MachineIntegerType::Int32 => Domain::Int32,
            MachineIntegerType::Int64 => Domain::Int64,
            _ => return None,
        };
        if self.contradictory {
            return Some(false);
        }
        let [a, b] = query.operands.each_ref().map(|p| p.operand_view());
        let mut read = Query::new(self);
        let tag = match query.operation {
            Op::Add => 0,
            Op::Subtract => 1,
            Op::Multiply => 2,
        } + if domain == Domain::Int64 { 5 } else { 0 };
        if let (Some(a), Some(b)) = (
            read.modular_resolve(domain, a),
            read.modular_resolve(domain, b),
        ) && self
            .no_overflow
            .contains(&overflow_key(tag, a, b, query.operation != Op::Subtract))
        {
            return Some(false);
        }
        let (a0, a1) = read.interval(domain, a);
        let (b0, b1) = read.interval(domain, b);
        let (lo, hi) = match query.operation {
            Op::Add => (a0 + b0, a1 + b1),
            Op::Subtract => read.difference(domain, a, b),
            Op::Multiply => {
                let p = [a0 * b0, a0 * b1, a1 * b0, a1 * b1];
                (*p.iter().min()?, *p.iter().max()?)
            }
        };
        let (min, max) = domain.range();
        (lo >= min && hi <= max).then_some(false)
    }
}
impl<'a> Query<'a> {
    fn new(graph: &'a DifferenceGraph) -> Self {
        Self {
            graph,
            frames: Vec::new(),
        }
    }
    fn depend(&mut self, input: Read) {
        if let Some((reads, _)) = self.frames.last_mut() {
            reads.push(input);
        }
    }
    fn uncacheable(&mut self) {
        if let Some((_, cacheable)) = self.frames.last_mut() {
            *cacheable = false;
        }
    }
    fn begin(&mut self, key: QueryKey) -> Option<Answer> {
        self.depend(Read::Query(key));
        // A native conditional can re-enter graph decisions while resolving
        // an operand. Hold the cache lock only for lookup or insertion, never
        // across that recursive work.
        let hit = self.graph.shared_queries.lock().get(&key);
        if hit.is_none() {
            self.frames.push((Vec::new(), true));
        }
        hit
    }
    fn finish(&mut self, key: QueryKey, root: &crate::kernel::KernelTerm, answer: Answer) {
        let (reads, cacheable) = self.frames.pop().expect("range query frame");
        if cacheable {
            self.graph
                .shared_queries
                .lock()
                .insert(key, root, answer, reads);
        } else {
            self.uncacheable();
        }
    }
    fn affine_interval(&mut self, (node, offset): Affine) -> (i128, i128) {
        let Some(node) = node else {
            return (offset, offset);
        };
        self.depend(Read::Truncation);
        let graph = self.graph;
        let (low, high) = graph.read_interval_observed(node, |node| self.depend(Read::Node(node)));
        (low + offset, high + offset)
    }
    fn difference_bound(&mut self, from: Affine, to: Affine) -> i128 {
        let by_intervals = self.affine_interval(to).1 - self.affine_interval(from).0;
        let graph = self.graph;
        let by_path = match (from.0, to.0) {
            (Some(from_node), Some(to_node)) => graph
                .shortest_from_observed(from_node, |node| self.depend(Read::Node(node)))
                .get(&to_node)
                .map(|distance| distance + to.1 - from.1),
            _ => None,
        };
        by_path.map_or(by_intervals, |path| path.min(by_intervals))
    }
    fn known_reading(&mut self, signed: Affine) -> Option<Affine> {
        DifferenceGraph::unsigned_reading(signed, |base| self.affine_interval(base))
    }
    fn known_flip(&mut self, domain: Domain, base: Affine) -> Option<Affine> {
        DifferenceGraph::flip_reading(domain, base, |base| self.affine_interval(base))
    }
    fn resolve_atom(&mut self, domain: Domain, atom: &MachineTerm) -> Option<Affine> {
        if let Some(value) = constant(domain, atom) {
            return Some((None, value));
        }
        self.depend(Read::Operand(
            domain,
            Key::for_format(format(domain), V::Legacy(atom)),
        ));
        if let Some(node) = self.graph.nodes.get(&(domain, atom.clone())) {
            return Some((Some(*node), 0));
        }
        if domain == Domain::UInt32 {
            let signed = self.resolve_atom(Domain::Int32, atom)?;
            return self.known_reading(signed);
        }
        None
    }
    /// Whether the facts bound `term` above zero. A remainder by a divisor
    /// that may be zero is an opaque value and bounds nothing.
    fn nonzero(&mut self, domain: Domain, term: V<'_>) -> bool {
        self.interval(domain, term).0 >= 1
    }

    fn resolve(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        if let V::Legacy(term) = term {
            self.uncacheable();
            return self.graph.resolve(domain, term);
        }
        let V::Shared(root) = term else {
            unreachable!()
        };
        let key = (Kind::Resolve, domain, root.id());
        if let Some(Answer::Resolve(hit)) = self.begin(key) {
            return hit;
        }
        let result = if let Some(atom) = atom(term) {
            self.resolve_atom(domain, &atom)
        } else {
            self.resolve_uncached(domain, term)
        };
        self.finish(key, root, Answer::Resolve(result));
        result
    }
    fn resolve_uncached(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        let key = Key::for_format(format(domain), term);
        self.depend(Read::Operand(domain, key.clone()));
        if let Some(affine) = self.graph.operand_affines.get(&(domain, key)) {
            return Some(*affine);
        }
        if let Some(base) = sign_flip_view(domain, term) {
            let base = self.resolve(domain, base)?;
            return self.known_flip(domain, base);
        }
        if domain == Domain::UInt32 {
            let base = self.resolve(Domain::Int32, term)?;
            return self.known_reading(base);
        }
        let (base_domain, base, offset, nonnegative) = link_parts_view(domain, term)?;
        let base = self.resolve(base_domain, base)?;
        link_fits(self.affine_interval(base), offset, domain, nonnegative)
            .then_some((base.0, base.1 + offset))
    }
    fn modular_resolve(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        if let V::Legacy(term) = term {
            self.uncacheable();
            return self.graph.modular_resolve(domain, term);
        }
        let V::Shared(root) = term else {
            unreachable!()
        };
        let key = (Kind::ModularResolve, domain, root.id());
        if let Some(Answer::Resolve(hit)) = self.begin(key) {
            return hit;
        }
        let result = if let Some((base, k)) = modular_parts_view(domain, term) {
            self.modular_resolve(domain, base)
                .map(|(node, offset)| (node, wrap(domain, offset + k)))
        } else {
            self.resolve(domain, term)
                .map(|(node, offset)| (node, wrap(domain, offset)))
        };
        self.finish(key, root, Answer::Resolve(result));
        result
    }
    fn interval(&mut self, domain: Domain, term: V<'_>) -> (i128, i128) {
        if let V::Legacy(term) = term {
            self.uncacheable();
            return self.graph.term_interval(domain, term);
        }
        let V::Shared(root) = term else {
            unreachable!()
        };
        let key = (Kind::Interval, domain, root.id());
        if let Some(Answer::Interval(hit)) = self.begin(key) {
            return hit;
        }
        let result = self.interval_uncached(domain, term);
        self.finish(key, root, Answer::Interval(result));
        result
    }
    fn interval_uncached(&mut self, domain: Domain, term: V<'_>) -> (i128, i128) {
        let (n0, n1) = self
            .resolve(domain, term)
            .map_or_else(|| domain.range(), |a| self.affine_interval(a));
        let (s0, s1) = self.structural(domain, term);
        let other = match domain {
            Domain::Int64 => Some(Domain::UInt64),
            Domain::UInt64 => Some(Domain::Int64),
            _ => None,
        };
        let (o0, o1) = other.and_then(|d| self.resolve(d, term)).map_or_else(
            || domain.range(),
            |a| {
                let (lo, hi) = self.affine_interval(a);
                wrap_interval(domain, lo, hi)
            },
        );
        (n0.max(s0).max(o0), n1.min(s1).min(o1))
    }
    fn difference(&mut self, domain: Domain, a: V<'_>, b: V<'_>) -> (i128, i128) {
        if Key::for_format(format(domain), a) == Key::for_format(format(domain), b) {
            return (0, 0);
        }
        let (a0, a1) = self.interval(domain, a);
        let (b0, b1) = self.interval(domain, b);
        let (mut lo, mut hi) = (a0 - b1, a1 - b0);
        if let (Some(a), Some(b)) = (self.resolve(domain, a), self.resolve(domain, b)) {
            hi = hi.min(self.difference_bound(b, a));
            lo = lo.max(-self.difference_bound(a, b));
        }
        (lo, hi)
    }
    fn structural(&mut self, domain: Domain, term: V<'_>) -> (i128, i128) {
        use MachineBinaryOp as Op;
        use MachineIntegerType as M;
        if domain == Domain::UInt32 {
            if let Some((ty, Op::BitwiseAnd, [a, b])) = term.binary()
                && matches!(ty, M::Int32 | M::UInt32)
                && let Some((mask, value)) = constant_view(domain, b)
                    .map(|k| (k, a))
                    .or_else(|| constant_view(domain, a).map(|k| (k, b)))
            {
                charge();
                let (lo, hi) = self.interval(domain, value);
                return if lo == hi {
                    (lo & mask, lo & mask)
                } else {
                    (0, hi.min(mask))
                };
            }
            charge();
            let (lo, hi) = self.interval(Domain::Int32, term);
            return wrap_interval(domain, lo, hi);
        }
        charge();
        let result = if let Some((encoding, source, destination, value)) = term.cast() {
            match (domain, encoding) {
                (Domain::Int32, E::Generic)
                    if crate::kernel::is_narrow_widening32(source, destination) =>
                {
                    self.interval(Domain::Narrow(source), value)
                }
                (Domain::Int32, E::Generic)
                    if crate::kernel::is_sign_cast32(source, destination) =>
                {
                    self.interval(domain, value)
                }
                (Domain::Int32, E::UInt32From64) => {
                    let (lo, hi) = self.interval(word_domain_view(value), value);
                    wrap_interval(domain, lo, hi)
                }
                (Domain::Int64, E::Int64From32) => self.interval(Domain::Int32, value),
                (Domain::UInt64, E::UInt64From32) => self.interval(Domain::UInt32, value),
                (Domain::Int64 | Domain::UInt64, E::Generic)
                    if matches!(source, M::Int64 | M::UInt64)
                        && matches!(destination, M::Int64 | M::UInt64) =>
                {
                    let (lo, hi) = self.interval(
                        if source == M::Int64 {
                            Domain::Int64
                        } else {
                            Domain::UInt64
                        },
                        value,
                    );
                    wrap_interval(domain, lo, hi)
                }
                (Domain::UInt64, E::UInt64FromInt64) => {
                    let (lo, hi) = self.interval(Domain::Int64, value);
                    wrap_interval(domain, lo, hi)
                }
                (Domain::Int64, E::Int64FromUInt32) => {
                    let (lo, hi) = self.interval(Domain::Int32, value);
                    if lo >= 0 {
                        (lo, hi)
                    } else if hi < 0 {
                        (lo + (1 << 32), hi + (1 << 32))
                    } else {
                        (0, (1 << 32) - 1)
                    }
                }
                _ => return domain.range(),
            }
        } else if let Some((ty, op, [a, b])) = term.binary() {
            if !binary_domain(domain, ty) {
                return domain.range();
            }
            match op {
                Op::Add => {
                    let (a0, a1) = self.interval(domain, a);
                    let (b0, b1) = self.interval(domain, b);
                    (a0 + b0, a1 + b1)
                }
                Op::Subtract => {
                    if domain == Domain::UInt64
                        && let Some((M::UInt64, Op::Remainder, [x, k])) = b.binary()
                        && Key::for_format(M::UInt64, a) == Key::for_format(M::UInt64, x)
                    {
                        let (a0, a1) = self.interval(domain, a);
                        let (k0, k1) = self.interval(domain, k);
                        if k0 < 1 {
                            return domain.range();
                        }
                        if k0 == k1 {
                            (a0 / k0 * k0, a1 / k0 * k0)
                        } else {
                            ((a0 - (k1 - 1)).max(0), a1)
                        }
                    } else {
                        self.difference(domain, a, b)
                    }
                }
                Op::Multiply if domain != Domain::UInt64 => {
                    let (a0, a1) = self.interval(domain, a);
                    let (b0, b1) = self.interval(domain, b);
                    let p = [a0 * b0, a0 * b1, a1 * b0, a1 * b1];
                    (*p.iter().min().unwrap(), *p.iter().max().unwrap())
                }
                Op::Divide | Op::Remainder if domain == Domain::Int32 && ty == M::UInt32 => {
                    let (lo, hi) = self.interval(domain, a);
                    let (a0, a1) = wrap_range((0, (1 << 32) - 1), lo, hi);
                    let (lo, hi) = self.interval(domain, b);
                    let (b0, b1) = wrap_range((0, (1 << 32) - 1), lo, hi);
                    if b0 < 1 {
                        return domain.range();
                    }
                    let (lo, hi) = if op == Op::Divide {
                        (a0 / b1, a1 / b0)
                    } else if a0 == a1 && b0 == b1 {
                        (a0 % b0, a0 % b0)
                    } else {
                        (0, a1.min(b1 - 1))
                    };
                    wrap_interval(domain, lo, hi)
                }
                Op::Divide | Op::Remainder => {
                    let (a0, a1) = self.interval(domain, a);
                    let (b0, b1) = self.interval(domain, b);
                    if b0 <= 0 && b1 >= 0 {
                        return domain.range();
                    }
                    if domain == Domain::UInt64 {
                        if op == Op::Divide {
                            (a0 / b1, a1 / b0)
                        } else if a0 == a1 && b0 == b1 {
                            (a0 % b0, a0 % b0)
                        } else {
                            (0, a1.min(b1 - 1))
                        }
                    } else if op == Op::Divide {
                        let q = [a0 / b0, a0 / b1, a1 / b0, a1 / b1];
                        (*q.iter().min().unwrap(), *q.iter().max().unwrap())
                    } else {
                        let bound = b0.abs().max(b1.abs()) - 1;
                        if a0 == a1 && b0 == b1 {
                            (a0 % b0, a0 % b0)
                        } else if a0 >= 0 {
                            (0, a1.min(bound))
                        } else if a1 <= 0 {
                            (a0.max(-bound), 0)
                        } else {
                            (-bound, bound)
                        }
                    }
                }
                Op::BitwiseXor if sign_flip_view(domain, term).is_some() => {
                    let base = sign_flip_view(domain, term).unwrap();
                    let (lo, hi) = self.interval(domain, base);
                    if lo >= 0 || hi < 0 {
                        let (a, b) = (flip_sign(domain, lo), flip_sign(domain, hi));
                        (a.min(b), a.max(b))
                    } else {
                        return domain.range();
                    }
                }
                Op::BitwiseAnd if domain == Domain::UInt64 => {
                    let Some((mask, value)) = constant_view(domain, b)
                        .map(|k| (k, a))
                        .or_else(|| constant_view(domain, a).map(|k| (k, b)))
                    else {
                        return domain.range();
                    };
                    let (lo, hi) = self.interval(domain, value);
                    if lo == hi {
                        (lo & mask, lo & mask)
                    } else {
                        (0, hi.min(mask))
                    }
                }
                _ => return domain.range(),
            }
        } else {
            return domain.range();
        };
        let (min, max) = domain.range();
        if result.0 >= min && result.1 <= max {
            result
        } else {
            (min, max)
        }
    }
}
fn word_domain_view(term: V<'_>) -> Domain {
    if let V::Legacy(term) = term {
        return word_domain(term);
    }
    if matches!(term.literal(), Some(uint64_constant!(_)))
        || matches!(
            term.binary(),
            Some((
                MachineIntegerType::UInt64,
                MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr
                    | MachineBinaryOp::BitwiseXor,
                _
            ))
        )
        || matches!(
            term.cast(),
            Some((
                E::UInt64From32 | E::UInt64FromInt32 | E::UInt64FromInt64,
                _,
                _,
                _
            ))
        )
        || matches!(
            term.unary(),
            Some((MachineIntegerType::UInt64, MachineUnaryOp::BitwiseNot, _))
        )
    {
        Domain::UInt64
    } else {
        Domain::Int64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::machine_integer::{Operation as Op, definedness::OverflowQueryView};
    use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm, Variable};

    #[test]
    fn named_read_bounds_are_available_to_structural_indices() {
        use crate::kernel::{
            CMemory, CValue, LoadKind, Pointer, VerificationSession, intern_c_memory,
        };
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(998_301));
        let memory = intern_c_memory(CMemory::new());
        let name = crate::kernel::eval::load_variable_for_cell(&memory, &address, LoadKind::Int32);
        let read = crate::kernel::eval::registered_load_term_for_variable(&name).unwrap();
        let named = MachineTerm::Variable(name);
        let lower = MachineTerm::Variable(Variable(998_302));
        let upper = MachineTerm::Variable(Variable(998_303));
        let equal = ConditionTerm::equal(named.clone(), lower.clone());
        let bound = ConditionTerm::signed_less_than(lower.clone(), upper.clone());
        for facts in [
            [equal.clone(), bound.clone()],
            [bound.clone(), equal.clone()],
        ] {
            let mut graph = DifferenceGraph::new();
            for fact in facts {
                graph.assume_condition(&fact, true);
            }
            for index in [named.clone(), read.clone()] {
                assert_eq!(
                    graph.decide(&ConditionTerm::signed_less_equal(
                        lower.clone(),
                        index.clone()
                    )),
                    Some(true)
                );
                assert_eq!(
                    graph.decide(&ConditionTerm::signed_less_than(index, upper.clone())),
                    Some(true)
                );
            }
            let shared = SharedMachineIntegerTerm::index(MachineIntegerType::Int32, read.clone());
            assert_eq!(
                graph.decide_word_equality_views(shared.operand_view(), V::Legacy(&lower)),
                Some(true)
            );
            let changed = intern_c_memory(
                memory
                    .memory()
                    .clone()
                    .store(address.clone(), CValue::Int32(17u32.into())),
            );
            let other =
                MachineTerm::MemoryLoad(changed, Box::new(address.clone()), LoadKind::Int32);
            assert_eq!(
                graph.decide(&ConditionTerm::signed_less_than(other, upper.clone())),
                None
            );
            assert_eq!(
                graph.decide(&ConditionTerm::signed_less_than(
                    read.clone(),
                    lower.clone()
                )),
                Some(false)
            );
        }
    }

    #[test]
    fn graph_overflow_views_keep_chained_bounds_and_unknown_answers() {
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let word = |value: i64| {
                if ty == MachineIntegerType::Int32 {
                    MachineTerm::constant(value as u32)
                } else {
                    MachineTerm::int64_constant(value)
                }
            };
            let x = MachineTerm::Variable(Variable(997801));
            let n = MachineTerm::Variable(Variable(997802));
            let native = |op, left, right| MachineTerm::Binary {
                format: ty,
                op,
                left: Box::new(left),
                right: Box::new(right),
            };
            let twice = native(MachineBinaryOp::Multiply, word(2), x.clone());
            let limit = if ty == MachineIntegerType::Int32 {
                1073741823
            } else {
                100
            };
            let mut bounded = DifferenceGraph::new();
            for condition in [
                ConditionTerm::machine_compare(ty, CompareRelation::LessEqual, word(0), x.clone()),
                ConditionTerm::machine_compare(ty, CompareRelation::LessThan, x.clone(), n.clone()),
                ConditionTerm::machine_compare(ty, CompareRelation::LessEqual, n, word(limit)),
            ] {
                bounded.assume_condition(&condition, true);
            }
            for graph in [DifferenceGraph::new(), bounded] {
                for (operation, left, right) in [
                    (Op::Add, twice.clone(), word(2)),
                    (Op::Subtract, twice.clone(), twice.clone()),
                    (Op::Multiply, x.clone(), word(2)),
                ] {
                    let expected = graph.decide(
                        &crate::kernel::machine_integer::representation::overflow_condition(
                            ty,
                            operation,
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        )
                        .unwrap(),
                    );
                    let shared = |term: &MachineTerm| {
                        SharedMachineIntegerTerm::from_shared(
                            ty,
                            KernelTermImport::default()
                                .machine_arithmetic(ty, term)
                                .unwrap(),
                        )
                        .unwrap()
                    };
                    let (a, b) = (shared(&left), shared(&right));
                    let query = OverflowQueryView::from_operands(
                        ty,
                        operation,
                        [a.operand_view(), b.operand_view()],
                    )
                    .unwrap();
                    let before = KernelTermExport::machine_export_count();
                    assert_eq!(graph.decide_overflow_query(&query), expected);
                    assert_eq!(KernelTermExport::machine_export_count(), before);
                    assert!(!a.has_boxed_operand());
                    assert!(!b.has_boxed_operand());
                }
            }
        }
    }

    #[test]
    fn graph_interval_views_match_native_operations_and_casts() {
        let _session = crate::kernel::VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(997811));
        let mut graph = DifferenceGraph::new();
        graph.assume_condition(&ConditionTerm::signed_less_equal(2.into(), x.clone()), true);
        graph.assume_condition(&ConditionTerm::signed_less_equal(x.clone(), 4.into()), true);
        let mut cases = Vec::new();
        for op in [
            MachineBinaryOp::Add,
            MachineBinaryOp::Subtract,
            MachineBinaryOp::Multiply,
            MachineBinaryOp::Divide,
            MachineBinaryOp::Remainder,
            MachineBinaryOp::BitwiseAnd,
            MachineBinaryOp::BitwiseXor,
        ] {
            for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt32] {
                cases.push((
                    Domain::Int32,
                    ty,
                    MachineTerm::Binary {
                        format: ty,
                        op,
                        left: Box::new(x.clone()),
                        right: Box::new(MachineTerm::constant(3)),
                    },
                ));
            }
        }
        cases.extend([
            (
                Domain::Int64,
                MachineIntegerType::Int64,
                MachineTerm::int64_from_32(x.clone()),
            ),
            (
                Domain::Int64,
                MachineIntegerType::Int64,
                MachineTerm::int64_from_uint32(x.clone()),
            ),
            (
                Domain::UInt64,
                MachineIntegerType::UInt64,
                MachineTerm::uint64_from_32(x.clone()),
            ),
        ]);
        for (domain, ty, term) in cases {
            let root = KernelTermImport::default()
                .machine_arithmetic(ty, &term)
                .unwrap();
            let before = KernelTermExport::machine_export_count();
            let mut query = Query::new(&graph);
            assert_eq!(
                query.interval(domain, V::Shared(&root)),
                graph.term_interval(domain, &term),
                "{domain:?} {term:?}"
            );
            assert_eq!(KernelTermExport::machine_export_count(), before);
        }
    }
    #[test]
    fn graph_overflow_views_reuse_original_compound_nodes_in_one_branch() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = MachineTerm::Variable(Variable(997821));
        let y = MachineTerm::Variable(Variable(997822));
        let product = MachineTerm::multiply(x, y.clone());
        let source = ConditionTerm::signed_add_overflows(product.clone(), y.clone());
        let parent = DifferenceGraph::new();
        let mut child = parent.clone();
        child.assume_condition(&source, false);
        let shared = |term: &MachineTerm| {
            SharedMachineIntegerTerm::from_shared(
                ty,
                KernelTermImport::default()
                    .machine_arithmetic(ty, term)
                    .unwrap(),
            )
            .unwrap()
        };
        let (a, b) = (shared(&product), shared(&y));
        let query =
            OverflowQueryView::from_operands(ty, Op::Add, [a.operand_view(), b.operand_view()])
                .unwrap();
        let before = KernelTermExport::machine_export_count();
        assert_eq!(parent.decide_overflow_query(&query), None);
        assert_eq!(child.decide_overflow_query(&query), Some(false));
        assert_eq!(parent.decide_overflow_query(&query), None);
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn shared_graph_order_preserves_direct_edges_and_negative_answers() {
        use crate::kernel::machine_integer::comparison::{
            comparison_view, condition_for_operand_views,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let two = match ty {
                MachineIntegerType::Int64 => MachineTerm::int64_constant(2),
                MachineIntegerType::UInt64 => MachineTerm::uint64_constant(2),
                _ => MachineTerm::constant(2),
            };
            let left = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Add,
                left: Box::new(MachineTerm::Variable(Variable(997851))),
                right: Box::new(two),
            };
            let right = MachineTerm::Variable(Variable(997852));
            let mut graph = DifferenceGraph::new();
            graph.assume_condition(
                &ConditionTerm::machine_compare(
                    ty,
                    CompareRelation::LessThan,
                    left.clone(),
                    right.clone(),
                ),
                true,
            );
            let left_root = KernelTermImport::default()
                .machine_arithmetic(ty, &left)
                .unwrap();
            let right_root = KernelTermImport::default()
                .machine_arithmetic(ty, &right)
                .unwrap();
            for relation in [
                CompareRelation::LessThan,
                CompareRelation::LessEqual,
                CompareRelation::GreaterThan,
                CompareRelation::GreaterEqual,
            ] {
                let native =
                    ConditionTerm::machine_compare(ty, relation, left.clone(), right.clone());
                let observed = condition_for_operand_views(
                    ty,
                    relation,
                    [V::Shared(&left_root), V::Shared(&right_root)],
                );
                let view = comparison_view(&observed, true).unwrap();
                let before = KernelTermExport::machine_export_count();
                assert_eq!(
                    graph.decide_shared_order(&view),
                    graph.decide(&native),
                    "{ty:?} {relation:?}"
                );
                assert_eq!(KernelTermExport::machine_export_count(), before);
            }
        }
    }

    #[test]
    fn shared_order_admission_matches_native_and_invalidates_only_its_branch() {
        use crate::kernel::machine_integer::comparison::{
            comparison_view, condition_for_operand_views,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let word = |n| match ty {
                MachineIntegerType::Int64 => MachineTerm::int64_constant(n),
                MachineIntegerType::UInt64 => MachineTerm::uint64_constant(n as u64),
                _ => MachineTerm::constant(n as u32),
            };
            let native_left = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Multiply,
                left: Box::new(MachineTerm::Variable(Variable(997861))),
                right: Box::new(word(3)),
            };
            let native_right = MachineTerm::Variable(Variable(997862));
            let left = KernelTermImport::default()
                .machine_arithmetic(ty, &native_left)
                .unwrap();
            let right = KernelTermImport::default()
                .machine_arithmetic(ty, &native_right)
                .unwrap();
            for truth in [false, true] {
                let source = condition_for_operand_views(
                    ty,
                    CompareRelation::LessThan,
                    [V::Shared(&left), V::Shared(&right)],
                );
                let query = comparison_view(&source, true).unwrap();
                let parent = DifferenceGraph::new();
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(parent.decide_shared_order(&query), None);
                let mut child = parent.clone();
                child.assume_condition(&source, truth);
                let mut native = DifferenceGraph::new();
                native.assume_condition(
                    &ConditionTerm::machine_compare(
                        ty,
                        CompareRelation::LessThan,
                        native_left.clone(),
                        native_right.clone(),
                    ),
                    truth,
                );
                assert_eq!(child.decide_shared_order(&query), Some(truth));
                assert_eq!(native.decide_shared_order(&query), Some(truth));
                assert_eq!(parent.decide_shared_order(&query), None);
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/difference_graph/operand_views/tests.rs");
    }
}
