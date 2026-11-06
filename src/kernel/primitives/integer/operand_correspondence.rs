//! Structural correspondence of shared operands. Cache only syntax and the
//! read/variable leaf pairs left to check; registry lookups and proof authority stay
//! with the caller and are never cached here.
use super::*;
use crate::persistent::PersistentMap;

type Key = (MachineIntegerType, u64, u64);
type Pairs = PersistentMap<(u64, u64), (KernelTerm, KernelTerm)>;
thread_local! {
    static PAIRS: std::cell::RefCell<HashMap<Key, Option<Pairs>>> = Default::default();
}

pub(super) fn clear() {
    PAIRS.with(|pairs| pairs.borrow_mut().clear());
}

pub(crate) fn shared_operand_leaf_pairs(
    format: MachineIntegerType,
    left: &KernelTerm,
    right: &KernelTerm,
) -> Option<Pairs> {
    use MachineOperandView::Shared as V;
    // End the borrow before a caller checks the returned load pairs: that
    // check can itself ask a structural comparison question.
    PAIRS.with(|pairs| {
        let mut pairs = pairs.borrow_mut();
        let mut pending = vec![(format, left, right, false)];
        while let Some((format, left, right, finish)) = pending.pop() {
            let key = (format, left.id(), right.id());
            if pairs.contains_key(&key) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if left == right {
                pairs.insert(key, Some(Pairs::default()));
                continue;
            }
            let (a, b) = (V(left), V(right));
            if (a.variable().is_some() || a.read().is_some())
                && (b.variable().is_some() || b.read().is_some())
            {
                pairs.insert(
                    key,
                    Some(
                        Pairs::default()
                            .with_inserted((left.id(), right.id()), (left.clone(), right.clone())),
                    ),
                );
                continue;
            }
            if let (Some(a), Some(b)) = (a.literal(), b.literal()) {
                let a = format.constant_from_term(&a);
                let b = format.constant_from_term(&b);
                pairs.insert(
                    key,
                    a.zip(b)
                        .filter(|(a, b)| a.bits() == b.bits())
                        .map(|_| Pairs::default()),
                );
                continue;
            }
            let children = if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
                (a.binary(), b.binary())
            {
                (af == bf && ao == bo).then_some(vec![(af, al, bl), (af, ar, br)])
            } else if let (Some((af, ao, av)), Some((bf, bo, bv))) = (a.unary(), b.unary()) {
                (af == bf && ao == bo).then_some(vec![(af, av, bv)])
            } else if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (a.cast(), b.cast()) {
                (ae == be && af == bf && at == bt).then_some(vec![(af, av, bv)])
            } else {
                None
            };
            let Some(children) = children else {
                pairs.insert(key, None);
                continue;
            };
            let children: Vec<_> = children
                .into_iter()
                .map(|(format, a, b)| {
                    let (V(a), V(b)) = (a, b) else {
                        unreachable!("shared children");
                    };
                    (format, a, b)
                })
                .collect();
            if !finish {
                pending.push((format, left, right, true));
                pending.extend(children.into_iter().map(|(f, a, b)| (f, a, b, false)));
                continue;
            }
            let mut result = Some(Pairs::default());
            for (format, a, b) in children {
                let Some(child) = &pairs[&(format, a.id(), b.id())] else {
                    result = None;
                    break;
                };
                let current = result.as_mut().expect("matching prefix");
                if current.shares_root_with(child) {
                    continue;
                }
                let (large, small) = if current.len() >= child.len() {
                    (&*current, child)
                } else {
                    (child, &*current)
                };
                let mut combined = large.clone();
                for (key, pair) in small.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    combined = combined.with_inserted(*key, pair.clone());
                }
                *current = combined;
            }
            pairs.insert(key, result);
        }
        pairs[&(format, left.id(), right.id())].clone()
    })
}
