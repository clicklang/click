//! The existing additive multiset rule, retaining DAG multiplicities rather
//! than expanding a shared occurrence once for every path to it.
use crate::kernel::{MachineBinaryOp as Op, MachineIntegerType, MachineOperandView as V};
use num_bigint::BigUint;
use std::collections::{HashMap, HashSet};

type Identity = (bool, u64);
fn identity(view: V<'_>) -> Identity {
    match view {
        V::Shared(root) => (true, root.id()),
        // Only a query-local visitation key, never a semantic term identity.
        V::Legacy(term) => (false, term as *const _ as usize as u64),
    }
}

pub(in crate::kernel::assumptions) fn parts(
    root: V<'_>,
    format: MachineIntegerType,
) -> (Vec<(V<'_>, BigUint)>, u32) {
    let mut seen = HashSet::new();
    let mut pending = vec![(root, false)];
    let mut order = Vec::new();
    while let Some((term, finish)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if finish {
            order.push(term);
            continue;
        }
        if !seen.insert(identity(term)) {
            continue;
        }
        pending.push((term, true));
        if let Some((ty, Op::Add, [a, b])) = term.binary()
            && ty == format
        {
            pending.extend([(b, false), (a, false)]);
        }
    }
    let mut counts = HashMap::from([(identity(root), BigUint::from(1u32))]);
    let mut leaves = Vec::new();
    let mut constant = 0u32;
    for term in order.into_iter().rev() {
        let count = counts
            .remove(&identity(term))
            .expect("reachable additive node");
        crate::instrumentation::record_deterministic_work(1);
        if let Some((ty, Op::Add, [a, b])) = term.binary()
            && ty == format
        {
            *counts.entry(identity(a)).or_default() += &count;
            *counts.entry(identity(b)).or_default() += count;
        } else if let Some(value) = term.word32_constant() {
            let low = count.iter_u32_digits().next().unwrap_or(0);
            constant = constant.wrapping_add(value.wrapping_mul(low));
        } else {
            leaves.push((term, count));
        }
    }
    // The reverse topological walk sees the rightmost leaves first.
    leaves.reverse();
    (leaves, constant)
}
