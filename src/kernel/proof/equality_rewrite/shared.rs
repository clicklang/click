//! Retained arithmetic reconstruction for exact equality substitution.
//! These are the existing rewrite constructors, not lowering or comparison
//! normalization. In particular, 32-bit sums/differences only fold literals.
use super::*;
use MachineBinaryOp as O;
use MachineIntegerType as T;

fn literal(term: &KernelTerm) -> Option<MachineTerm> {
    MachineOperandView::Shared(term).literal()
}
fn imported(format: T, term: &MachineTerm) -> KernelTerm {
    KernelTermImport::default()
        .machine_arithmetic(format, term)
        .expect("arithmetic reconstruction")
}
fn constant(format: T, bits: u64) -> KernelTerm {
    imported(
        format,
        &match format {
            T::Int32 => MachineTerm::constant(bits as u32),
            T::UInt32 => MachineTerm::uint32_constant(bits as u32),
            T::Int64 => MachineTerm::int64_constant(bits as i64),
            T::UInt64 => MachineTerm::uint64_constant(bits),
            _ => MachineTerm::narrow_constant(format, u128::from(bits)),
        },
    )
}
fn word(term: &KernelTerm) -> Option<u32> {
    literal(term)?.constant32()
}
fn wide(term: &KernelTerm, format: T) -> Option<u64> {
    let value = literal(term)?;
    match format {
        T::Int64 => value.int64_as_const().map(|v| v as u64),
        T::UInt64 => value.uint64_as_const(),
        _ => None,
    }
}
fn binary_parts(term: &KernelTerm, format: T, op: O) -> Option<[&KernelTerm; 2]> {
    match term.node() {
        KernelTermNode::MachineBinary {
            format: found,
            operator,
            arguments,
        } if *found == format && *operator == op => Some(arguments.each_ref()),
        _ => None,
    }
}
fn restyle(format: T, term: KernelTerm) -> KernelTerm {
    if let Some(value) = literal(&term) {
        imported(format, &value.constant_in32(format))
    } else {
        term.with_machine_observation_type(format)
    }
}

thread_local! {
    static BINARY: RefCell<HashMap<(T, O, u64, u64), KernelTerm>> = Default::default();
    static STATIC: RefCell<HashMap<u64, bool>> = Default::default();
    static REWRITTEN: RefCell<HashMap<(KernelTerm, KernelTerm, u64), KernelTerm>> = Default::default();
}
pub(in crate::kernel) fn clear() {
    BINARY.with(|cache| cache.borrow_mut().clear());
    STATIC.with(|cache| cache.borrow_mut().clear());
    REWRITTEN.with(|cache| cache.borrow_mut().clear());
}

pub(super) fn binary(format: T, op: O, left: KernelTerm, right: KernelTerm) -> KernelTerm {
    let key = (format, op, left.id(), right.id());
    if let Some(found) = BINARY.with(|cache| cache.borrow().get(&key).cloned()) {
        return found;
    }
    let result = binary_uncached(format, op, left, right);
    BINARY.with(|cache| cache.borrow_mut().insert(key, result.clone()));
    result
}
fn binary_uncached(format: T, op: O, mut left: KernelTerm, mut right: KernelTerm) -> KernelTerm {
    crate::instrumentation::record_deterministic_work(1);
    let raw = |left, right| KernelTerm::machine_binary_shared(format, op, [left, right]);
    if matches!(format, T::Int32 | T::UInt32) {
        if matches!(op, O::Add | O::Subtract) {
            return match (word(&left), word(&right)) {
                (Some(a), Some(b)) => constant(
                    format,
                    u64::from(if op == O::Add {
                        a.wrapping_add(b)
                    } else {
                        a.wrapping_sub(b)
                    }),
                ),
                _ => raw(left, right),
            };
        }
        left = restyle(format, left);
        right = restyle(format, right);
        let (a, b) = (word(&left), word(&right));
        match op {
            O::Multiply => match (a, b) {
                (Some(a), Some(b)) => return constant(format, u64::from(a.wrapping_mul(b))),
                (_, Some(1)) => return left,
                (Some(1), _) => return right,
                (_, Some(0)) | (Some(0), _) => return constant(format, 0),
                _ => {}
            },
            O::BitwiseAnd => match (a, b) {
                (Some(a), Some(b)) => return constant(format, u64::from(a & b)),
                (_, Some(u32::MAX)) => return left,
                (Some(u32::MAX), _) => return right,
                (_, Some(0)) | (Some(0), _) => return constant(format, 0),
                _ if left == right => return left,
                _ => {}
            },
            O::ShiftLeft => match (a, b) {
                (Some(a), Some(b)) if b < 32 => {
                    return constant(format, u64::from(a.wrapping_shl(b)));
                }
                (_, Some(0)) => return left,
                _ => {}
            },
            _ => {} // Every other 32-bit binary rewrite is a raw node.
        }
        return raw(left, right);
    }
    // Two literal leaves use the existing width-specific constructor. No
    // symbolic operand is exported to evaluate this fixed-size operation.
    if let (Some(a), Some(b)) = (literal(&left), literal(&right)) {
        return imported(format, &MachineTerm::machine_binary(format, op, a, b));
    }
    let (a, b) = (wide(&left, format), wide(&right, format));
    if matches!(format, T::Int64 | T::UInt64) && op == O::Multiply {
        match (a, b) {
            (_, Some(1)) => return left,
            (Some(1), _) => return right,
            (_, Some(0)) | (Some(0), _) => return constant(format, 0),
            _ => {}
        }
    }
    if format == T::Int64 && op == O::Subtract && left == right {
        return constant(format, 0);
    }
    if format != T::UInt64 {
        return raw(left, right);
    }
    match op {
        O::Add | O::Subtract => {
            if b == Some(0) {
                return left;
            }
            if op == O::Add && a == Some(0) {
                return right;
            }
            if op == O::Subtract
                && MachineOperandView::Shared(&left)
                    .variable()
                    .zip(MachineOperandView::Shared(&right).variable())
                    .is_some_and(|(a, b)| a == b)
            {
                return constant(format, 0);
            }
            let opposite = if op == O::Add { O::Subtract } else { O::Add };
            if let (Some([inner, taken]), Some(b)) = (binary_parts(&left, format, opposite), b)
                && wide(taken, format) == Some(b)
            {
                return inner.clone();
            }
        }
        O::BitwiseAnd => {
            if let (Some([inner_left, inner_right]), Some(outer)) =
                (binary_parts(&left, format, O::BitwiseAnd), b)
            {
                let next = match (wide(inner_left, format), wide(inner_right, format)) {
                    (None, Some(mask)) => Some((inner_left, mask)),
                    (Some(mask), None) => Some((inner_right, mask)),
                    _ => None,
                };
                if let Some((inner, mask)) = next {
                    return binary(format, op, inner.clone(), constant(format, mask & outer));
                }
            }
            if a == Some(0) || b == Some(0) {
                return constant(format, 0);
            }
            if let (Some([inner_left, inner_right]), Some(mask)) =
                (binary_parts(&left, format, O::BitwiseOr), b)
            {
                let next = match (wide(inner_left, format), wide(inner_right, format)) {
                    (None, Some(value)) => Some((inner_left, value)),
                    (Some(value), None) => Some((inner_right, value)),
                    _ => None,
                };
                if let Some((inner, value)) = next {
                    return binary(
                        format,
                        O::BitwiseOr,
                        binary(format, O::BitwiseAnd, inner.clone(), constant(format, mask)),
                        constant(format, value & mask),
                    );
                }
            }
        }
        O::BitwiseOr => {
            if let (Some([x, y]), Some(value)) = (binary_parts(&left, format, O::BitwiseAnd), b)
                && wide(x, format)
                    .or_else(|| wide(y, format))
                    .is_some_and(|mask| mask & !value == 0)
            {
                return constant(format, value);
            }
            if a == Some(0) {
                return right;
            }
            if b == Some(0) {
                return left;
            }
        }
        _ => {}
    }
    raw(left, right)
}

pub(super) fn unary(format: T, op: MachineUnaryOp, operand: KernelTerm) -> KernelTerm {
    if matches!(format, T::Int32 | T::UInt32) {
        let operand = literal(&operand)
            .map(|v| imported(format, &v.constant_word32()))
            .unwrap_or(operand);
        return KernelTerm::machine_unary_shared(format, op, operand);
    }
    if let Some(value) = literal(&operand) {
        return imported(format, &MachineTerm::machine_unary(format, op, value));
    }
    KernelTerm::machine_unary_shared(format, op, operand)
}

fn leaf(term: &KernelTerm) -> Option<MachineTerm> {
    if let Some(variable) = MachineOperandView::Shared(term).variable() {
        Some(MachineTerm::Variable(*variable))
    } else {
        literal(term).or_else(|| term.machine_conversion_leaf().cloned())
    }
}
fn format(term: &KernelTerm) -> T {
    let KernelType::C(ty) = term.ty() else {
        unreachable!("shared machine carrier")
    };
    T::from_c_type(*ty).expect("machine format")
}
fn children(term: &KernelTerm) -> Vec<&KernelTerm> {
    match term.node() {
        KernelTermNode::MachineBinary { arguments, .. } => arguments.iter().collect(),
        KernelTermNode::MachineUnary { operand, .. }
        | KernelTermNode::MachineCast { operand, .. } => vec![operand],
        _ => vec![],
    }
}
fn cast(
    encoding: MachineCastSpelling,
    source: T,
    destination: T,
    operand: KernelTerm,
) -> KernelTerm {
    if encoding == MachineCastSpelling::Generic {
        operand.checking_machine_cast_preserving_sign_pairs(source, destination)
    } else if let Some(value) = literal(&operand) {
        // Legacy exact-rewrite constructors preserve their literal spelling,
        // notably Word32 (not UInt32) for the low-word conversion.
        let cast = MachineTerm::legacy_cast(encoding, Box::new(value));
        let (operator, value) = cast.as_unary().expect("legacy cast");
        imported(destination, &operator.build(value.clone()))
    } else {
        operand.checking_legacy_machine_conversion(source, destination)
    }
}

/// Existing load canonicalization over a retained carrier. Operator rebuilding
/// is raw, except generic casts, exactly as in the native canonical walk.
fn canonical(root: &KernelTerm) -> Option<(HashMap<u64, KernelTerm>, HashMap<u64, bool>)> {
    let mut values = HashMap::<u64, KernelTerm>::new();
    let mut loads = HashMap::<u64, bool>::new();
    let mut pending = vec![(root, false)];
    while let Some((term, finish)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if values.contains_key(&term.id()) {
            continue;
        }
        let nodes = children(term);
        if !finish && !nodes.is_empty() {
            pending.push((term, true));
            pending.extend(nodes.into_iter().map(|child| (child, false)));
            continue;
        }
        let has_load = if nodes.is_empty() {
            leaf(term).is_some_and(|value| crate::kernel::eval::term_mentions_a_memory_load(&value))
        } else {
            nodes.iter().any(|node| loads[&node.id()])
        };
        loads.insert(term.id(), has_load);
        let value = match term.node() {
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            } => {
                let [mut a, mut b] = arguments.each_ref().map(|t| values[&t.id()].clone());
                if matches!(format, T::Int32 | T::UInt32) {
                    a = restyle(*format, a);
                    b = restyle(*format, b);
                }
                KernelTerm::machine_binary_shared(*format, *operator, [a, b])
            }
            KernelTermNode::MachineUnary {
                format,
                operator,
                operand,
            } => {
                let mut operand = values[&operand.id()].clone();
                if matches!(format, T::Int32 | T::UInt32) {
                    operand = literal(&operand)
                        .map(|v| imported(*format, &v.constant_word32()))
                        .unwrap_or(operand);
                }
                KernelTerm::machine_unary_shared(*format, *operator, operand)
            }
            KernelTermNode::MachineCast {
                encoding,
                source,
                destination,
                operand,
            } => {
                let operand = values[&operand.id()].clone();
                if *encoding == MachineCastSpelling::Generic {
                    cast(*encoding, *source, *destination, operand)
                } else {
                    let operand = if matches!(
                        encoding,
                        MachineCastSpelling::Int64From32
                            | MachineCastSpelling::UInt64From32
                            | MachineCastSpelling::Int64FromUInt32
                            | MachineCastSpelling::UInt64FromInt32
                    ) {
                        literal(&operand)
                            .map(|v| imported(*source, &v.constant_word32()))
                            .unwrap_or(operand)
                    } else {
                        operand
                    };
                    KernelTerm::machine_cast_shared(*encoding, *source, *destination, operand)
                }
            }
            _ => KernelTermImport::default().machine_arithmetic(
                format(term),
                &crate::kernel::eval::canonical_term(&leaf(term)?),
            )?,
        }
        .with_machine_observation_type(format(term));
        values.insert(term.id(), value);
    }
    Some((values, loads))
}

/// The only native callback receives an atomic leaf, including a retained
/// Integer-conversion payload. Shared arithmetic is matched and rebuilt here.
/// A result outside the shared fragment is an explicit producer boundary.
pub(super) fn rewrite(
    root: &KernelTerm,
    from: &MachineTerm,
    to: &MachineTerm,
    rewrite_leaf: impl Fn(&MachineTerm) -> MachineTerm,
) -> Option<KernelTerm> {
    let from_has_load = crate::kernel::eval::term_mentions_a_memory_load(from);
    let root_has_load = if root.has_machine_conversions() {
        crate::kernel::shared_machine_conversion_leaves(root, || {
            !crate::instrumentation::deadline_exceeded()
        })?
        .iter()
        .any(|(_, node)| {
            node.machine_conversion_leaf()
                .is_some_and(crate::kernel::eval::term_mentions_a_memory_load)
        })
    } else {
        false
    };
    let canonical_values = if from_has_load || root_has_load {
        Some(canonical(root)?)
    } else {
        None
    };
    let canonical_from = canonical_values
        .as_ref()
        .map(|_| crate::kernel::eval::canonical_term(from));
    let mut sources = HashMap::<T, Option<KernelTerm>>::new();
    let mut canonical_sources = HashMap::<T, Option<KernelTerm>>::new();
    let mut replacements = HashMap::<T, Option<KernelTerm>>::new();
    let mut values = HashMap::<u64, KernelTerm>::new();
    let mut pending = vec![(root, false)];
    while let Some((term, finish)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return Some(root.clone());
        }
        if values.contains_key(&term.id()) {
            continue;
        }
        let ty = format(term);
        let source = sources
            .entry(ty)
            .or_insert_with(|| KernelTermImport::default().machine_arithmetic(ty, from));
        let cache_key = if canonical_values.is_none() && static_syntax(term)? {
            source
                .clone()
                .zip(
                    replacements
                        .entry(ty)
                        .or_insert_with(|| KernelTermImport::default().machine_arithmetic(ty, to))
                        .clone(),
                )
                .map(|(from, to)| (from, to, term.id()))
        } else {
            None
        };
        if let Some(found) = cache_key
            .as_ref()
            .and_then(|key| REWRITTEN.with(|cache| cache.borrow().get(key).cloned()))
        {
            values.insert(term.id(), found);
            continue;
        }
        let canonical_match = canonical_from.as_ref().is_some_and(|from| {
            let (values, loads) = canonical_values.as_ref().expect("canonical source");
            if !from_has_load && !loads[&term.id()] {
                return false;
            }
            canonical_sources
                .entry(ty)
                .or_insert_with(|| KernelTermImport::default().machine_arithmetic(ty, from))
                .as_ref()
                == values.get(&term.id())
        });
        if source.as_ref() == Some(term) || canonical_match {
            let replacement = replacements
                .entry(ty)
                .or_insert_with(|| KernelTermImport::default().machine_arithmetic(ty, to))
                .clone()?;
            values.insert(term.id(), replacement);
            continue;
        }
        let nodes = children(term);
        if !finish && !nodes.is_empty() {
            pending.push((term, true));
            pending.extend(nodes.into_iter().map(|child| (child, false)));
            continue;
        }
        let value = match term.node() {
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            } => binary(
                *format,
                *operator,
                values[&arguments[0].id()].clone(),
                values[&arguments[1].id()].clone(),
            ),
            KernelTermNode::MachineUnary {
                format,
                operator,
                operand,
            } => unary(*format, *operator, values[&operand.id()].clone()),
            KernelTermNode::MachineCast {
                encoding,
                source,
                destination,
                operand,
            } => cast(
                *encoding,
                *source,
                *destination,
                values[&operand.id()].clone(),
            ),
            _ => KernelTermImport::default().machine_arithmetic(ty, &rewrite_leaf(&leaf(term)?))?,
        }
        .with_machine_observation_type(ty);
        if let Some(key) = cache_key {
            REWRITTEN.with(|cache| cache.borrow_mut().insert(key, value.clone()));
        }
        values.insert(term.id(), value);
    }
    values.remove(&root.id())
}

/// Reserved load-variable IDs are structural. Ordinary variables can never
/// acquire a load origin, so their rewrites may survive registry/fact changes.
/// Conversion payloads and load variables retain a query-local traversal.
fn static_syntax(root: &KernelTerm) -> Option<bool> {
    STATIC.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![(root, false)];
        while let Some((term, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            if cache.contains_key(&term.id()) {
                continue;
            }
            let nodes = children(term);
            if !finish && !nodes.is_empty() {
                pending.push((term, true));
                pending.extend(nodes.into_iter().map(|child| (child, false)));
                continue;
            }
            let value = match term.node() {
                KernelTermNode::Variable(variable) => !crate::kernel::is_load_variable(variable),
                KernelTermNode::MachineLiteral(_) => true,
                KernelTermNode::IntegerToMachine { .. } => false,
                _ => nodes.iter().all(|node| cache[&node.id()]),
            };
            cache.insert(term.id(), value);
        }
        Some(cache[&root.id()])
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn differential(format: T) {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1006000));
        let y = MachineTerm::Variable(Variable(1006001));
        let c = |bits| KernelTermExport::machine(&constant(format, bits)).unwrap();
        let raw = |op, a, b| MachineTerm::Binary {
            format,
            op,
            left: Box::new(a),
            right: Box::new(b),
        };
        let pairs = [
            (x.clone(), y.clone()),
            (x.clone(), c(0)),
            (c(1), x.clone()),
            (c(7), c(3)),
            (x.clone(), x.clone()),
            (c(u64::MAX), x.clone()),
            (raw(O::Add, x.clone(), c(7)), c(7)),
            (raw(O::Subtract, x.clone(), c(7)), c(7)),
            (raw(O::BitwiseAnd, x.clone(), c(3)), c(1)),
            (raw(O::BitwiseOr, x.clone(), c(3)), c(1)),
        ];
        for op in [
            O::Add,
            O::Subtract,
            O::Multiply,
            O::Divide,
            O::Remainder,
            O::BitwiseAnd,
            O::BitwiseOr,
            O::BitwiseXor,
            O::ShiftLeft,
            O::ShiftRight,
        ] {
            if format.format().bits() < 32
                && !crate::kernel::primitives::is_native_narrow_operator(op)
            {
                continue;
            }
            for (a, b) in &pairs {
                let native = raw(op, a.clone(), b.clone());
                let root = imported(format, &native);
                for to in [y.clone(), c(0), c(1), c(u64::MAX)] {
                    let expected = super::super::rewrite_term(&native, &x, &to);
                    let exports = KernelTermExport::machine_export_count();
                    let found = rewrite(&root, &x, &to, |leaf| {
                        super::super::rewrite_term(leaf, &x, &to)
                    })
                    .expect("shared result");
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    assert_eq!(
                        KernelTermExport::machine(&found).unwrap(),
                        expected,
                        "{format:?} {op:?}: {native:?} -> {to:?}"
                    );
                }
            }
        }
    }
    #[test]
    fn exact_rewrite_shared_casts_unaries_and_literal_recovery_match_native() {
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(Variable(1006100));
        let y = MachineTerm::Variable(Variable(1006101));
        let mut terms = Vec::new();
        for ty in [T::Int8, T::UInt16, T::Int32, T::UInt32, T::Int64, T::UInt64] {
            let zero = KernelTermExport::machine(&constant(ty, 0)).unwrap();
            terms.push((
                ty,
                MachineTerm::Unary {
                    format: ty,
                    op: MachineUnaryOp::BitwiseNot,
                    operand: Box::new(x.clone()),
                },
                zero.clone(),
            ));
            for destination in [T::Int8, T::UInt16, T::Int32, T::UInt32, T::Int64, T::UInt64] {
                terms.push((
                    destination,
                    MachineTerm::Cast {
                        spelling: MachineCastSpelling::Generic,
                        from: ty,
                        to: destination,
                        value: Box::new(x.clone()),
                    },
                    zero.clone(),
                ));
            }
        }
        for encoding in [
            MachineCastSpelling::Int64From32,
            MachineCastSpelling::UInt64From32,
            MachineCastSpelling::UInt32From64,
            MachineCastSpelling::Int64FromUInt32,
            MachineCastSpelling::UInt64FromInt32,
            MachineCastSpelling::UInt64FromInt64,
        ] {
            let (source, destination) = encoding.legacy_formats().unwrap();
            let zero = KernelTermExport::machine(&constant(source, 0)).unwrap();
            terms.push((
                destination,
                MachineTerm::legacy_cast(encoding, Box::new(x.clone())),
                zero.clone(),
            ));
            for operand in [
                MachineTerm::Binary {
                    format: source,
                    op: O::Add,
                    left: Box::new(x.clone()),
                    right: Box::new(zero.clone()),
                },
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: T::Int32,
                    to: source,
                    value: Box::new(x.clone()),
                },
            ] {
                terms.push((
                    destination,
                    MachineTerm::legacy_cast(encoding, Box::new(operand)),
                    zero.clone(),
                ));
            }
        }
        for (ty, native, zero) in terms {
            for to in [zero, y.clone()] {
                let root = imported(ty, &native);
                let expected = super::super::rewrite_term(&native, &x, &to);
                let exports = KernelTermExport::machine_export_count();
                let found = rewrite(&root, &x, &to, |leaf| {
                    super::super::rewrite_term(leaf, &x, &to)
                })
                .unwrap();
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert_eq!(
                    KernelTermExport::machine(&found).unwrap(),
                    expected,
                    "{native:?} -> {to:?}"
                );
            }
        }
        for (ty, native) in [
            (T::Int64, MachineTerm::int64_constant(-1)),
            (T::UInt64, MachineTerm::uint64_constant(u64::MAX)),
            (T::UInt64, MachineTerm::uint64_constant(u64::from(u32::MAX))),
        ] {
            let from = MachineTerm::constant(u32::MAX);
            let root = imported(ty, &native);
            let expected = super::super::rewrite_term(&native, &from, &y);
            let found = rewrite(&root, &from, &y, |leaf| {
                super::super::rewrite_term(leaf, &from, &y)
            })
            .unwrap();
            assert_eq!(KernelTermExport::machine(&found).unwrap(), expected);
        }
    }

    #[test]
    fn exact_rewrite_shared_load_matching_uses_current_registry_and_canonical_source() {
        let _session = VerificationSession::enter();
        let pointer = CMemory::global_pointer("shared-exact-load");
        let memory = intern_c_memory(CMemory::new().with_block("shared-exact-load", 16));
        let raw =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let named = crate::kernel::eval::canonical_term(&raw);
        assert!(matches!(named, MachineTerm::Variable(_)));
        let add = |value| MachineTerm::Binary {
            format: T::Int32,
            op: O::Add,
            left: Box::new(value),
            right: Box::new(MachineTerm::uint32_constant(1)),
        };
        let native = add(named);
        let from = add(raw);
        let to = MachineTerm::constant(9);
        let root = imported(T::Int32, &native);
        let expected = super::super::rewrite_term(&native, &from, &to);
        assert_eq!(expected, to);
        let exports = KernelTermExport::machine_export_count();
        let found = rewrite(&root, &from, &to, |leaf| {
            super::super::rewrite_term(leaf, &from, &to)
        })
        .unwrap();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(KernelTermExport::machine(&found).unwrap(), expected);

        let index = MachineTerm::Variable(Variable(1006200));
        let indexed = pointer.offset_by_int32_elements(index.clone());
        let read = crate::kernel::eval::load_variable_for_cell(&memory, &indexed, LoadKind::Int32);
        let native = MachineTerm::Variable(read);
        let root = imported(T::Int32, &native);
        let one = MachineTerm::constant(1);
        let expected = super::super::rewrite_term(&native, &index, &one);
        assert_ne!(expected, native);
        let found = rewrite(&root, &index, &one, |leaf| {
            super::super::rewrite_term(leaf, &index, &one)
        })
        .unwrap();
        assert_eq!(KernelTermExport::machine(&found).unwrap(), expected);
        crate::kernel::eval::clear_load_variable_registry();
        let expected = super::super::rewrite_term(&native, &index, &one);
        assert_eq!(expected, native);
        let found = rewrite(&root, &index, &one, |leaf| {
            super::super::rewrite_term(leaf, &index, &one)
        })
        .unwrap();
        assert_eq!(KernelTermExport::machine(&found).unwrap(), expected);
    }

    mod scaling_tests {
        use super::*;
        include!("../../../scaling_tests/kernel/proof/equality_rewrite/shared.rs");
    }

    macro_rules! parity {
        ($name:ident, $ty:ident) => {
            #[test]
            fn $name() {
                differential(T::$ty);
            }
        };
    }
    parity!(exact_rewrite_shared_int8_constructor_parity, Int8);
    parity!(exact_rewrite_shared_uint8_constructor_parity, UInt8);
    parity!(exact_rewrite_shared_int16_constructor_parity, Int16);
    parity!(exact_rewrite_shared_uint16_constructor_parity, UInt16);
    parity!(exact_rewrite_shared_int32_constructor_parity, Int32);
    parity!(exact_rewrite_shared_uint32_constructor_parity, UInt32);
    parity!(exact_rewrite_shared_int64_constructor_parity, Int64);
    parity!(exact_rewrite_shared_uint64_constructor_parity, UInt64);
}
