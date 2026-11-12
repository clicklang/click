//! Smart constructors used by exact-load normalization, preserving native syntax.
use super::*;

pub(in crate::kernel) fn normalize_node(
    node: &KernelTerm,
    children: &[KernelTerm],
) -> Option<KernelTerm> {
    let result = match node.node() {
        KernelTermNode::MachineBinary {
            format: ty,
            operator,
            ..
        } if matches!(ty, T::Int32 | T::UInt32) => {
            let [left, right] = children else { return None };
            binary32(*ty, *operator, left.clone(), right.clone())
        }
        KernelTermNode::MachineUnary {
            format: ty,
            operator,
            ..
        } if matches!(ty, T::Int32 | T::UInt32) => {
            let operand = children.first()?;
            if let Some(native) = leaf(operand) {
                retained(*ty, &MachineTerm::machine_unary(*ty, *operator, native))
            } else if let KernelTermNode::MachineUnary {
                format: inner,
                operator: inner_op,
                operand: child,
            } = operand.node()
                && inner == ty
                && inner_op == operator
            {
                child.clone()
            } else {
                KernelTerm::machine_unary_shared(*ty, *operator, restyle(*ty, operand.clone()))
            }
        }
        _ => return transport_node(node, children),
    };
    Some(result.with_machine_observation_type(format(node)))
}

fn binary32(ty: T, op: O, left: KernelTerm, right: KernelTerm) -> KernelTerm {
    if let (Some(a), Some(b)) = (leaf(&left), leaf(&right)) {
        return retained(ty, &MachineTerm::machine_binary(ty, op, a, b));
    }
    if matches!(op, O::Add | O::Subtract) {
        return sum32(ty, op, left, right);
    }
    let (left, right) = (restyle(ty, left), restyle(ty, right));
    let (a, b) = (word(&left), word(&right));
    match op {
        O::Divide if b == Some(1) => return left,
        O::ShiftRight if b == Some(0) => return left,
        O::ShiftLeft if ty == T::Int32 => {
            return KernelTerm::machine_binary_shared(ty, op, [left, right]);
        }
        O::BitwiseAnd | O::BitwiseOr
            if crate::kernel::shared_machine_syntax_equal(&left, &right) =>
        {
            return left;
        }
        O::BitwiseOr => match (a, b) {
            (_, Some(0)) => return left,
            (Some(0), _) => return right,
            (_, Some(u32::MAX)) | (Some(u32::MAX), _) => return constant(ty, u64::from(u32::MAX)),
            _ => {}
        },
        O::BitwiseXor => return xor(ty, left, right),
        _ => {}
    }
    binary(ty, op, left, right)
}

// Match MachineTerm's derived ordering without exporting shared children. The
// header contains only the variant's scalar fields; equal headers are followed
// by a lexicographic comparison of children. Opaque leaves retain native order.
fn syntax_cmp(left: &KernelTerm, right: &KernelTerm) -> std::cmp::Ordering {
    fn header(node: &KernelTerm) -> MachineTerm {
        let zero = || Box::new(MachineTerm::constant(0));
        match node.node() {
            KernelTermNode::MachineIf { arguments } => MachineTerm::If {
                condition: Box::new(
                    KernelTermExport::condition(&arguments[0]).expect("conditional guard"),
                ),
                then_term: zero(),
                else_term: zero(),
            },
            KernelTermNode::MachineBinary {
                format, operator, ..
            } => MachineTerm::Binary {
                format: *format,
                op: *operator,
                left: zero(),
                right: zero(),
            },
            KernelTermNode::MachineUnary {
                format, operator, ..
            } => MachineTerm::Unary {
                format: *format,
                op: *operator,
                operand: zero(),
            },
            KernelTermNode::MachineCast {
                encoding,
                source,
                destination,
                ..
            } => MachineTerm::Cast {
                spelling: *encoding,
                from: *source,
                to: *destination,
                value: zero(),
            },
            _ => leaf(node).expect("retained machine leaf"),
        }
    }
    enum Task<'a> {
        Nodes(&'a KernelTerm, &'a KernelTerm),
        Order(std::cmp::Ordering),
    }
    let mut pending = vec![Task::Nodes(left, right)];
    let mut seen = std::collections::HashSet::new();
    while let Some(task) = pending.pop() {
        let (a, b) = match task {
            Task::Order(order) if !order.is_eq() => return order,
            Task::Order(_) => continue,
            Task::Nodes(a, b) => (a, b),
        };
        crate::instrumentation::record_deterministic_work(1);
        if a == b || !seen.insert((a.id(), b.id())) {
            continue;
        }
        // Cast's native declaration compares its child before its formats.
        if let (
            KernelTermNode::MachineCast {
                encoding: ae,
                source: af,
                destination: at,
                operand: av,
            },
            KernelTermNode::MachineCast {
                encoding: be,
                source: bf,
                destination: bt,
                operand: bv,
            },
        ) = (a.node(), b.node())
        {
            let order = ae.cmp(be);
            if !order.is_eq() {
                return order;
            }
            pending.push(Task::Order(af.cmp(bf).then(at.cmp(bt))));
            pending.push(Task::Nodes(av, bv));
            continue;
        }
        let order = header(a).cmp(&header(b));
        if !order.is_eq() {
            return order;
        }
        pending.extend(
            children(a)
                .into_iter()
                .zip(children(b))
                .rev()
                .map(|(a, b)| Task::Nodes(a, b)),
        );
    }
    std::cmp::Ordering::Equal
}

fn xor(ty: T, left: KernelTerm, right: KernelTerm) -> KernelTerm {
    if crate::kernel::shared_machine_syntax_equal(&left, &right) {
        return constant(ty, 0);
    }
    // Inputs have already been normalized bottom-up, so their XOR chains have
    // no duplicate atoms. Merge their selected atoms; shared atoms remain DAGs.
    let mut pending = vec![left, right];
    let mut atoms = Vec::new();
    let mut bits = 0;
    while let Some(node) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = word(&node) {
            bits ^= value;
        } else if let Some([a, b]) = binary_parts(&node, ty, O::BitwiseXor) {
            pending.extend([a.clone(), b.clone()]);
        } else {
            atoms.push(node);
        }
    }
    atoms.sort_by(syntax_cmp);
    let mut normalized = Vec::new();
    let mut atoms = atoms.into_iter().peekable();
    while let Some(atom) = atoms.next() {
        if atoms
            .peek()
            .is_some_and(|next| syntax_cmp(&atom, next).is_eq())
        {
            atoms.next();
        } else {
            normalized.push(atom);
        }
    }
    if bits != 0 {
        normalized.push(constant(ty, u64::from(bits)));
        normalized.sort_by(syntax_cmp);
    }
    normalized
        .into_iter()
        .reduce(|a, b| KernelTerm::machine_binary_shared(ty, O::BitwiseXor, [a, b]))
        .unwrap_or_else(|| constant(ty, 0))
}

// Follow the native cancellation order. Each subtraction iteration removes
// selected addends; shared syntax equality is memoized independently of facts.
fn sum32(ty: T, op: O, mut left: KernelTerm, mut right: KernelTerm) -> KernelTerm {
    use crate::kernel::shared_machine_syntax_equal as equal;
    'reduce: loop {
        crate::instrumentation::record_deterministic_work(1);
        (left, right) = (restyle(ty, left), restyle(ty, right));
        if let (Some(a), Some(b)) = (word(&left), word(&right)) {
            return constant(
                ty,
                u64::from(if op == O::Add {
                    a.wrapping_add(b)
                } else {
                    a.wrapping_sub(b)
                }),
            );
        }
        if op == O::Add {
            for (sum, other) in [(&right, &left), (&left, &right)] {
                if let Some([base, sub]) = binary_parts(sum, ty, O::Subtract)
                    && equal(sub, other)
                {
                    return base.clone();
                }
            }
            for (negation, sum) in [(&left, &right), (&right, &left)] {
                if let (Some([zero, sub]), Some([a, b])) = (
                    binary_parts(negation, ty, O::Subtract),
                    binary_parts(sum, ty, O::Add),
                ) && word(zero) == Some(0)
                {
                    if equal(sub, a) {
                        return b.clone();
                    }
                    if equal(sub, b) {
                        return a.clone();
                    }
                }
            }
            if word(&right) == Some(0) {
                return left;
            }
            if word(&left) == Some(0) {
                return right;
            }
        } else {
            if word(&right) == Some(0) {
                return left;
            }
            if equal(&left, &right) {
                return constant(ty, 0);
            }
            if let (Some([a, b]), Some([c, d])) = (
                binary_parts(&left, ty, O::Add),
                binary_parts(&right, ty, O::Add),
            ) {
                let reduced = [(a, c, b, d), (a, d, b, c), (b, c, a, d), (b, d, a, c)]
                    .into_iter()
                    .find_map(|(x, y, rest_left, rest_right)| {
                        equal(x, y).then(|| (rest_left.clone(), rest_right.clone()))
                    });
                if let Some(reduced) = reduced {
                    (left, right) = reduced;
                    continue 'reduce;
                }
            }
            if let Some([a, b]) = binary_parts(&left, ty, O::Add) {
                if equal(a, &right) {
                    return b.clone();
                }
                if equal(b, &right) {
                    return a.clone();
                }
            }
            if let Some([a, b]) = binary_parts(&right, ty, O::Add) {
                if equal(&left, a) {
                    (left, right) = (constant(ty, 0), b.clone());
                    continue 'reduce;
                }
                if equal(&left, b) {
                    (left, right) = (constant(ty, 0), a.clone());
                    continue 'reduce;
                }
            }
        }
        return KernelTerm::machine_binary_shared(ty, op, [left, right]);
    }
}
