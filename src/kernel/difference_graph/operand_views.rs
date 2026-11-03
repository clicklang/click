//! Borrowed arithmetic queries over the existing difference graph.
use super::*;
use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
use crate::kernel::uint64_constant;
use crate::kernel::{KernelMachineCastEncoding as E, MachineOperandView as V};

fn format(domain: Domain) -> MachineIntegerType {
    match domain {
        Domain::Int32 => MachineIntegerType::Int32,
        Domain::UInt32 => MachineIntegerType::UInt32,
        Domain::Int64 => MachineIntegerType::Int64,
        Domain::UInt64 => MachineIntegerType::UInt64,
        Domain::Narrow(ty) => ty,
    }
}

fn atom(term: V<'_>) -> Option<Bitvector32Term> {
    term.literal()
        .or_else(|| term.variable().copied().map(Bitvector32Term::Variable))
}
fn constant_view(domain: Domain, term: V<'_>) -> Option<i128> {
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
fn link_parts_view(domain: Domain, term: V<'_>) -> Option<(Domain, V<'_>, i128, bool)> {
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
fn sign_flip_view(domain: Domain, term: V<'_>) -> Option<V<'_>> {
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

struct Query<'a> {
    graph: &'a DifferenceGraph,
    intervals: std::collections::BTreeMap<(Domain, u64), (i128, i128)>,
    resolved: std::collections::BTreeMap<(Domain, u64), Option<Affine>>,
}
impl DifferenceGraph {
    pub(super) fn index_operand_node(
        &mut self,
        domain: Domain,
        term: &Bitvector32Term,
        node: NodeId,
    ) {
        if matches!(term, Bitvector32Term::Variable(_)) || V::Legacy(term).literal().is_some() {
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
            self.operand_nodes.insert(
                (domain, Key::for_format(format(domain), V::Shared(&root))),
                node,
            );
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
        let mut read = Query {
            graph: self,
            intervals: Default::default(),
            resolved: Default::default(),
        };
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
impl Query<'_> {
    fn resolve(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        if let V::Legacy(term) = term {
            return self.graph.resolve(domain, term);
        }
        if let Some(atom) = atom(term) {
            return self.graph.resolve(domain, &atom);
        }
        let V::Shared(root) = term else {
            unreachable!()
        };
        let key = (domain, root.id());
        if let Some(hit) = self.resolved.get(&key) {
            return *hit;
        }
        let result = self.resolve_uncached(domain, term);
        self.resolved.insert(key, result);
        result
    }
    fn resolve_uncached(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        if let Some(node) = self
            .graph
            .operand_nodes
            .get(&(domain, Key::for_format(format(domain), term)))
        {
            return Some((Some(*node), 0));
        }
        if let Some(base) = sign_flip_view(domain, term) {
            let base = self.resolve(domain, base)?;
            return self.graph.known_flip(domain, base);
        }
        if domain == Domain::UInt32 {
            let base = self.resolve(Domain::Int32, term)?;
            return self.graph.known_reading(base);
        }
        let (base_domain, base, offset, nonnegative) = link_parts_view(domain, term)?;
        let base = self.resolve(base_domain, base)?;
        link_fits(
            self.graph.affine_interval(base),
            offset,
            domain,
            nonnegative,
        )
        .then_some((base.0, base.1 + offset))
    }
    fn modular_resolve(&mut self, domain: Domain, term: V<'_>) -> Option<Affine> {
        if let V::Legacy(term) = term {
            return self.graph.modular_resolve(domain, term);
        }
        if let Some((base, k)) = modular_parts_view(domain, term) {
            let (node, offset) = self.modular_resolve(domain, base)?;
            Some((node, wrap(domain, offset + k)))
        } else {
            let (node, offset) = self.resolve(domain, term)?;
            Some((node, wrap(domain, offset)))
        }
    }
    fn interval(&mut self, domain: Domain, term: V<'_>) -> (i128, i128) {
        if let V::Legacy(term) = term {
            return self.graph.term_interval(domain, term);
        }
        if let Some(atom) = atom(term) {
            return self.graph.term_interval(domain, &atom);
        }
        let V::Shared(root) = term else {
            unreachable!()
        };
        let key = (domain, root.id());
        if let Some(hit) = self.intervals.get(&key) {
            return *hit;
        }
        let (n0, n1) = self
            .resolve(domain, term)
            .map_or_else(|| domain.range(), |a| self.graph.affine_interval(a));
        let (s0, s1) = self.structural(domain, term);
        let other = match domain {
            Domain::Int64 => Some(Domain::UInt64),
            Domain::UInt64 => Some(Domain::Int64),
            _ => None,
        };
        let (o0, o1) = other.and_then(|d| self.resolve(d, term)).map_or_else(
            || domain.range(),
            |a| {
                let (lo, hi) = self.graph.affine_interval(a);
                wrap_interval(domain, lo, hi)
            },
        );
        let result = (n0.max(s0).max(o0), n1.min(s1).min(o1));
        self.intervals.insert(key, result);
        result
    }
    fn difference(&mut self, domain: Domain, a: V<'_>, b: V<'_>) -> (i128, i128) {
        if Key::for_format(format(domain), a) == Key::for_format(format(domain), b) {
            return (0, 0);
        }
        let (a0, a1) = self.interval(domain, a);
        let (b0, b1) = self.interval(domain, b);
        let (mut lo, mut hi) = (a0 - b1, a1 - b0);
        if let (Some(a), Some(b)) = (self.resolve(domain, a), self.resolve(domain, b)) {
            hi = hi.min(self.graph.difference_bound(b, a));
            lo = lo.max(-self.graph.difference_bound(a, b));
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
    fn graph_overflow_views_keep_chained_bounds_and_unknown_answers() {
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
            let word = |value: i64| {
                if ty == MachineIntegerType::Int32 {
                    Bitvector32Term::constant(value as u32)
                } else {
                    Bitvector32Term::int64_constant(value)
                }
            };
            let x = Bitvector32Term::Variable(Variable(997801));
            let n = Bitvector32Term::Variable(Variable(997802));
            let native = |op, left, right| Bitvector32Term::Binary {
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
                    let shared = |term: &Bitvector32Term| {
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
        let x = Bitvector32Term::Variable(Variable(997811));
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
                    Bitvector32Term::Binary {
                        format: ty,
                        op,
                        left: Box::new(x.clone()),
                        right: Box::new(Bitvector32Term::constant(3)),
                    },
                ));
            }
        }
        cases.extend([
            (
                Domain::Int64,
                MachineIntegerType::Int64,
                Bitvector32Term::int64_from_32(x.clone()),
            ),
            (
                Domain::Int64,
                MachineIntegerType::Int64,
                Bitvector32Term::int64_from_uint32(x.clone()),
            ),
            (
                Domain::UInt64,
                MachineIntegerType::UInt64,
                Bitvector32Term::uint64_from_32(x.clone()),
            ),
        ]);
        for (domain, ty, term) in cases {
            let root = KernelTermImport::default()
                .machine_arithmetic(ty, &term)
                .unwrap();
            let before = KernelTermExport::machine_export_count();
            let mut query = Query {
                graph: &graph,
                intervals: Default::default(),
                resolved: Default::default(),
            };
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
        let x = Bitvector32Term::Variable(Variable(997821));
        let y = Bitvector32Term::Variable(Variable(997822));
        let product = Bitvector32Term::multiply(x, y.clone());
        let source = ConditionTerm::signed_add_overflows(product.clone(), y.clone());
        let parent = DifferenceGraph::new();
        let mut child = parent.clone();
        child.assume_condition(&source, false);
        let shared = |term: &Bitvector32Term| {
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/difference_graph/operand_views/tests.rs");
    }
}
