//! Borrowed root views of machine operands. Inspecting a shared root never
//! requests its boxed expansion; child observations retain child handles.
use super::*;

// Only written machine variables are cached. Registered-load dependencies are
// resolved by each collector against its current registry, never cached here.
thread_local! {
    static SHARED_MACHINE_CARRIERS: std::cell::RefCell<HashMap<u64, crate::persistent::PersistentSet<Variable>>> = Default::default();
}

pub(crate) fn clear_shared_machine_variable_cache() {
    clear_shared_value_readings();
    KernelTerm::clear_cast_checks();
    SHARED_MACHINE_CARRIERS.with(|cache| cache.borrow_mut().clear());
}

/// Written variables of the shared arithmetic storage fragment. This summary
/// reads no proof facts or load registry; callers resolve dependencies in their
/// own collection mode after the cache borrow has ended. Partial summaries are
/// never cached when the caller's budget is exhausted.
pub(crate) fn shared_machine_syntax_variables(
    root: &KernelTerm,
    mut visit: impl FnMut() -> bool,
) -> Option<crate::persistent::PersistentSet<Variable>> {
    SHARED_MACHINE_CARRIERS.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut pending = vec![(root, false)];
        while let Some((term, finish)) = pending.pop() {
            if !visit() {
                return None;
            }
            if cache.contains_key(&term.id()) {
                continue;
            }
            let result = match term.node() {
                KernelTermNode::Variable(variable) => {
                    crate::persistent::PersistentSet::default().with_value(*variable)
                }
                KernelTermNode::MachineLiteral(_) => Default::default(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => {
                    if !finish {
                        pending.push((term, true));
                        pending.push((operand, false));
                        continue;
                    }
                    cache[&operand.id()].clone()
                }
                KernelTermNode::MachineBinary {
                    arguments: [left, right],
                    ..
                } => {
                    if !finish {
                        pending.push((term, true));
                        pending.push((right, false));
                        pending.push((left, false));
                        continue;
                    }
                    let (left, right) = (&cache[&left.id()], &cache[&right.id()]);
                    let (large, small) = if left.len() >= right.len() {
                        (left, right)
                    } else {
                        (right, left)
                    };
                    let mut result = large.clone();
                    if !large.shares_root_with(small) {
                        for variable in small.iter() {
                            if !visit() {
                                return None;
                            }
                            result = result.with_value(*variable);
                        }
                    }
                    result
                }
                _ => unreachable!("shared machine observation storage fragment"),
            };
            cache.insert(term.id(), result);
        }
        Some(cache[&root.id()].clone())
    })
}

// Value relations depend only on syntax. Cache each conversion edge once per
// verification, including refused readings; no fact-context identity is used.
thread_local! {
    static SHARED_VALUE_READINGS: std::cell::RefCell<HashMap<(MachineIntegerType, u64), Option<(MachineIntegerType, KernelTerm)>>> = Default::default();
}

pub(super) fn clear_shared_value_readings() {
    SHARED_VALUE_READINGS.with(|cache| cache.borrow_mut().clear());
}

pub(super) fn shared_value_reading(
    mut ty: MachineIntegerType,
    root: &KernelTerm,
) -> Option<(MachineIntegerType, KernelTerm)> {
    use crate::kernel::KernelMachineCastEncoding::Generic;
    SHARED_VALUE_READINGS.with(|cache| {
        let mut cache = cache.borrow_mut();
        let mut term = root.clone();
        let mut path = Vec::new();
        let result = loop {
            crate::instrumentation::record_deterministic_work(1);
            let key = (ty, term.id());
            if let Some(result) = cache.get(&key) {
                break result.clone();
            }
            path.push(key);
            // Rule W peels one 32-bit sign conversion before checking the
            // resulting root, exactly as machine_value_reading does.
            if matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32)
                && let KernelTermNode::MachineCast {
                    encoding: Generic,
                    source,
                    destination,
                    operand,
                } = term.node()
                && source.format().bits() == 32
                && destination.format().bits() == 32
                && source != destination
            {
                term = operand.clone();
            }
            if let KernelTermNode::MachineCast {
                encoding: Generic,
                source,
                destination,
                operand,
            } = term.node()
            {
                if *destination != ty
                    && ty.format().bits() <= 32
                    && ty.format().contains(destination.format())
                {
                    ty = *destination;
                    continue;
                }
                if *destination != ty {
                    break None;
                }
                if ty.format().bits() > source.format().bits()
                    && ty.format().contains(source.format())
                {
                    ty = *source;
                    term = operand.clone();
                    continue;
                }
            }
            if let KernelTermNode::MachineLiteral(value) = term.node()
                && ty.constant_from_term(&value.legacy_term()).is_none()
            {
                break None;
            }
            break Some((ty, term));
        };
        for key in path {
            cache.insert(key, result.clone());
        }
        result
    })
}

#[derive(Clone, Copy)]
pub(crate) enum MachineOperandView<'a> {
    Shared(&'a KernelTerm),
    Legacy(&'a Bitvector32Term),
}

impl SharedMachineIntegerTerm {
    /// Add the written generic cast root without invoking a folding constructor.
    pub(crate) fn cast_operand(&self, destination: MachineIntegerType) -> Self {
        if let Some(root) = self.shared_operand() {
            Self::from_shared(
                destination,
                KernelTerm::machine_cast_shared(
                    crate::kernel::KernelMachineCastEncoding::Generic,
                    self.ty(),
                    destination,
                    root.clone(),
                ),
            )
            .expect("cast over shared operand")
        } else {
            Self::intern(
                destination,
                Bitvector32Term::MachineIntegerCast {
                    value: Box::new(self.value().clone()),
                    source: self.ty(),
                    destination,
                },
            )
        }
    }

    pub(crate) fn operand_view(&self) -> MachineOperandView<'_> {
        match &self.0.operand {
            MachineIntegerOperand::Shared { term, .. } => MachineOperandView::Shared(term),
            MachineIntegerOperand::Legacy(value) => MachineOperandView::Legacy(value),
        }
    }
}

impl<'a> MachineOperandView<'a> {
    /// Retain the written carrier at one fixed interpretation for indexed
    /// matching. This changes no node and reads no proof facts.
    pub(crate) fn retain(self, ty: MachineIntegerType) -> SharedMachineIntegerTerm {
        match self {
            Self::Legacy(value) => SharedMachineIntegerTerm::intern(ty, value.clone()),
            Self::Shared(term) => {
                SharedMachineIntegerTerm::from_shared(ty, term.with_machine_observation_type(ty))
                    .expect("shared operand fragment")
            }
        }
    }

    pub(crate) fn accepts_cast_operand(mut self, mut ty: MachineIntegerType) -> bool {
        loop {
            if let Some(value) = self.literal() {
                return ty.constant_from_term(&value).is_some();
            }
            if self.variable().is_some() {
                return true;
            }
            if let Self::Legacy(value) = self {
                return ty.accepts_cast_operand(value);
            }
            if let Some((
                crate::kernel::KernelMachineCastEncoding::Generic,
                source,
                destination,
                operand,
            )) = self.cast()
            {
                if destination != ty {
                    return false;
                }
                if ty.format().bits() > source.format().bits()
                    && ty.format().contains(source.format())
                {
                    ty = source;
                    self = operand;
                    continue;
                }
                return true;
            }
            return ty.format().bits() != 128;
        }
    }

    pub(crate) fn cast(
        self,
    ) -> Option<(
        crate::kernel::KernelMachineCastEncoding,
        MachineIntegerType,
        MachineIntegerType,
        Self,
    )> {
        match self {
            Self::Shared(term) => match term.node() {
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => Some((*encoding, *source, *destination, Self::Shared(operand))),
                _ => None,
            },
            Self::Legacy(term) => {
                let (op, operand) = term.as_unary()?;
                let (encoding, source, destination) =
                    crate::kernel::KernelMachineCastEncoding::of_unary(op)?;
                Some((encoding, source, destination, Self::Legacy(operand)))
            }
        }
    }

    pub(crate) fn variable(self) -> Option<&'a Variable> {
        match self {
            Self::Shared(term) => match term.node() {
                KernelTermNode::Variable(variable) => Some(variable),
                _ => None,
            },
            Self::Legacy(Bitvector32Term::Variable(variable)) => Some(variable),
            Self::Legacy(_) => None,
        }
    }

    pub(crate) fn binary(self) -> Option<(MachineIntegerType, MachineBinaryOp, [Self; 2])> {
        match self {
            Self::Shared(term) => match term.node() {
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => Some((
                    *format,
                    *operator,
                    [Self::Shared(&arguments[0]), Self::Shared(&arguments[1])],
                )),
                _ => None,
            },
            Self::Legacy(Bitvector32Term::Binary {
                format,
                op,
                left,
                right,
            }) => Some((*format, *op, [Self::Legacy(left), Self::Legacy(right)])),
            Self::Legacy(_) => None,
        }
    }

    /// Literal payload only, without descending through an operation.
    pub(crate) fn literal(self) -> Option<Bitvector32Term> {
        match self {
            Self::Shared(term) if matches!(term.node(), KernelTermNode::MachineLiteral(_)) => {
                Some(KernelTermExport::machine(term).expect("machine literal"))
            }
            Self::Legacy(value) if is_machine_constant(value) => Some(value.clone()),
            _ => None,
        }
    }

    pub(crate) fn word32_constant(self) -> Option<u32> {
        match self {
            Self::Legacy(value) => value.as_const(),
            Self::Shared(term) => term.machine_constant_reading()?.legacy_term().as_const(),
        }
    }

    pub(crate) fn uint64_constant(self) -> Option<u64> {
        match self {
            Self::Legacy(value) => value.uint64_as_const(),
            Self::Shared(term) => term
                .machine_constant_reading()?
                .legacy_term()
                .uint64_as_const(),
        }
    }

    pub(crate) fn int64_constant(self) -> Option<i64> {
        match self {
            Self::Legacy(value) => value.int64_as_const(),
            Self::Shared(term) => term
                .machine_constant_reading()?
                .legacy_term()
                .int64_as_const(),
        }
    }

    /// The legacy int64 root-width range, without expanding a shared cast or
    /// arithmetic operand. Generic casts deliberately retain their old refusal.
    pub(crate) fn int64_width_interval(self) -> Option<(i64, i64)> {
        use crate::kernel::KernelMachineCastEncoding as E;
        if let Some(Bitvector32Term::Int64Constant(value)) = self.literal() {
            return Some((value, value));
        }
        match self.cast() {
            Some((E::Int64From32, _, _, _)) => {
                return Some((i64::from(i32::MIN), i64::from(i32::MAX)));
            }
            Some((E::Int64FromUInt32, _, _, _)) => return Some((0, i64::from(u32::MAX))),
            _ => {}
        }
        let (MachineIntegerType::Int64, MachineBinaryOp::BitwiseAnd, [left, right]) =
            self.binary()?
        else {
            return None;
        };
        let mask = left.int64_constant().or_else(|| right.int64_constant())?;
        (mask >= 0).then_some((0, mask))
    }

    pub(crate) fn root_width(self) -> Option<CarrierWidth> {
        match self {
            Self::Legacy(value) => crate::kernel::root_width(value),
            Self::Shared(term) => match term.node() {
                KernelTermNode::MachineBinary { format, .. }
                | KernelTermNode::MachineUnary { format, .. } => {
                    Some(CarrierWidth::of_machine_type(*format))
                }
                KernelTermNode::MachineCast { destination, .. } => {
                    Some(CarrierWidth::of_machine_type(*destination))
                }
                KernelTermNode::MachineLiteral(_) => crate::kernel::root_width(&self.literal()?),
                KernelTermNode::Variable(_) => None,
                _ => unreachable!("shared machine operand fragment"),
            },
        }
    }

    pub(crate) fn observe(self, ty: MachineIntegerType) -> Option<IntegerTerm> {
        if let Some(literal) = self.literal() {
            return IntegerTerm::from_machine(ty, literal);
        }
        match self {
            Self::Shared(term)
                if ty.format().bits() == 128
                    && !matches!(term.node(), KernelTermNode::Variable(_))
                    && !matches!(self.cast(), Some((crate::kernel::KernelMachineCastEncoding::Generic, source, destination, operand))
                        if destination == ty && operand.accepts_cast_operand(source)) =>
            {
                None
            }
            Self::Shared(term) => {
                let (read_ty, read) = if matches!(term.node(), KernelTermNode::MachineCast { .. }) {
                    shared_value_reading(ty, term)?
                } else {
                    (ty, term.clone())
                };
                if let KernelTermNode::MachineLiteral(value) = read.node() {
                    return Some(IntegerTerm::constant(
                        read_ty
                            .constant_from_term(&value.legacy_term())?
                            .to_integer(),
                    ));
                }
                let observed_ty = match term.node() {
                    KernelTermNode::MachineCast {
                        encoding: crate::kernel::KernelMachineCastEncoding::Generic,
                        destination,
                        ..
                    } if *destination != ty
                        && ty.format().bits() <= 32
                        && ty.format().contains(destination.format()) =>
                    {
                        *destination
                    }
                    _ => ty,
                };
                Some(IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(
                    observed_ty,
                    term.with_machine_observation_type(observed_ty),
                )?))
            }
            Self::Legacy(value) => IntegerTerm::from_machine(ty, value.clone()),
        }
    }

    /// Legacy leaves retain the existing read-over-write adapter. A shared
    /// variable can also name a read, but constructing that leaf costs O(1).
    /// Explicit shared operators are never recursively resolved here.
    pub(crate) fn read_source(self) -> Option<std::borrow::Cow<'a, Bitvector32Term>> {
        match self {
            Self::Legacy(value) => Some(std::borrow::Cow::Borrowed(value)),
            Self::Shared(term) => match term.node() {
                KernelTermNode::Variable(variable) => Some(std::borrow::Cow::Owned(
                    Bitvector32Term::Variable(*variable),
                )),
                _ => None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cached_machine_constants_match_legacy_readings() {
        let _session = crate::kernel::VerificationSession::enter();
        use MachineBinaryOp::*;
        for ty in crate::kernel::machine_integer::FORMATS {
            let literal = |n: i64| {
                ty.constant_term(
                    MachineIntegerConstant::from_bits(
                        ty.format(),
                        (n as u128) & ty.format().mask(),
                    )
                    .unwrap(),
                )
                .unwrap()
            };
            let check = |boxed: Bitvector32Term| {
                let shared = KernelTermImport::default().machine(ty, &boxed);
                let cached = shared.machine_constant_reading().map(|v| v.legacy_term());
                assert_eq!(
                    cached.as_ref().and_then(|v| v.as_const()),
                    boxed.as_const(),
                    "{boxed:?}"
                );
                assert_eq!(
                    cached.as_ref().and_then(|v| v.int64_as_const()),
                    boxed.int64_as_const(),
                    "{boxed:?}"
                );
                assert_eq!(
                    cached.as_ref().and_then(|v| v.uint64_as_const()),
                    boxed.uint64_as_const(),
                    "{boxed:?}"
                );
                assert!(matches!(
                    shared.node(),
                    KernelTermNode::MachineBinary { .. } | KernelTermNode::MachineUnary { .. }
                ));
            };
            for a in [
                0,
                1,
                -1,
                i32::MIN as i64,
                i32::MAX as i64,
                i64::MIN,
                i64::MAX,
            ] {
                check(Bitvector32Term::Unary {
                    format: ty,
                    op: MachineUnaryOp::BitwiseNot,
                    operand: Box::new(literal(a)),
                });
                for b in [0, 1, -1, 31, 32, 63, 64] {
                    for op in [
                        Add, Subtract, Multiply, Divide, Remainder, ShiftLeft, ShiftRight,
                        BitwiseAnd, BitwiseOr, BitwiseXor,
                    ] {
                        let inner = Bitvector32Term::Binary {
                            format: ty,
                            op,
                            left: Box::new(literal(a)),
                            right: Box::new(literal(b)),
                        };
                        check(inner.clone());
                        check(Bitvector32Term::Binary {
                            format: ty,
                            op: ShiftRight,
                            left: Box::new(literal(a)),
                            right: Box::new(inner.clone()),
                        });
                        check(Bitvector32Term::Binary {
                            format: ty,
                            op: Add,
                            left: Box::new(inner),
                            right: Box::new(literal(1)),
                        });
                    }
                }
            }
        }
    }

    #[test]
    fn operand_views_preserve_legacy_operation_readings() {
        use crate::kernel::machine_integer::{Operation, bounds, identity, representation};
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftRight,
            ] {
                let left = Bitvector32Term::Variable(Variable(956100));
                let right = ty
                    .constant_term(
                        MachineIntegerConstant::from_integer(ty.format(), &2.into()).unwrap(),
                    )
                    .unwrap();
                let boxed = Bitvector32Term::Binary {
                    format: ty,
                    op,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let shared = KernelTermImport::default().machine(ty, &boxed);
                let observation = SharedMachineIntegerTerm::from_shared(ty, shared).unwrap();
                let source = IntegerTerm::Machine(observation.clone());
                let expected =
                    representation::word_operation(ty, &boxed).map(|(operation, a, b)| {
                        (
                            ty,
                            operation.exact(
                                IntegerTerm::from_machine(ty, a.clone()).unwrap(),
                                IntegerTerm::from_machine(ty, b.clone()).unwrap(),
                            ),
                        )
                    });
                assert_eq!(identity::mathematical(&source), expected);
                let additive = representation::word_operation(ty, &boxed)
                    .is_some_and(|(op, _, _)| matches!(op, Operation::Add | Operation::Subtract));
                assert_eq!(
                    identity::additive_mathematical(&source),
                    additive.then_some(expected).flatten()
                );
                let view = observation.operand_view();
                let (_, _, [a, b]) = view.binary().unwrap();
                assert_eq!(a.observe(ty), IntegerTerm::from_machine(ty, left));
                assert_eq!(b.observe(ty), IntegerTerm::from_machine(ty, right));
                for upper in [false, true] {
                    let result = bounds::operation_bound(&observation, upper);
                    assert_eq!(
                        result.is_some(),
                        matches!(op, MachineBinaryOp::Divide | MachineBinaryOp::ShiftRight)
                            || op == MachineBinaryOp::Remainder
                                && (upper || ty.format().is_signed())
                    );
                }
                assert!(!observation.has_boxed_operand());
            }
        }
    }

    #[test]
    fn operand_view_observation_preserves_format_admission() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::UInt32;
        let boxed = Bitvector32Term::Binary {
            format: ty,
            op: MachineBinaryOp::Add,
            left: Box::new(Bitvector32Term::Variable(Variable(956101))),
            right: Box::new(Bitvector32Term::UInt32Constant(0)),
        };
        let shared = KernelTermImport::default().machine(ty, &boxed);
        for observed_ty in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
            MachineIntegerType::UInt128,
        ] {
            let actual = MachineOperandView::Shared(&shared).observe(observed_ty);
            if let Some(IntegerTerm::Machine(machine)) = &actual {
                assert!(!machine.has_boxed_operand());
            }
            assert_eq!(
                actual,
                IntegerTerm::from_machine(observed_ty, boxed.clone())
            );
        }
    }
}

#[cfg(test)]
mod cast_tests {
    use super::*;

    #[test]
    fn shared_widening_ranges_preserve_signedness_without_exporting() {
        use crate::kernel::{KernelMachineCastEncoding as E, KernelType};
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::C(MachineIntegerType::Int32.c_type()),
            Variable(985004),
        );
        for _ in 0..96 {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        for (encoding, source, destination, expected) in [
            (
                E::Int64From32,
                MachineIntegerType::Int32,
                MachineIntegerType::Int64,
                Some((i64::from(i32::MIN), i64::from(i32::MAX))),
            ),
            (
                E::Int64FromUInt32,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                Some((0, i64::from(u32::MAX))),
            ),
            (
                E::UInt64From32,
                MachineIntegerType::UInt32,
                MachineIntegerType::UInt64,
                None,
            ),
            (
                E::UInt64FromInt32,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                None,
            ),
            (
                E::UInt64FromInt64,
                MachineIntegerType::Int64,
                MachineIntegerType::UInt64,
                None,
            ),
            (
                E::UInt32From64,
                MachineIntegerType::UInt64,
                MachineIntegerType::UInt32,
                None,
            ),
            (
                E::Generic,
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                None,
            ),
        ] {
            let cast = KernelTerm::machine_cast_shared(
                encoding,
                source,
                destination,
                root.with_machine_observation_type(source),
            );
            let machine = SharedMachineIntegerTerm::from_shared(destination, cast).unwrap();
            assert_eq!(machine.operand_view().int64_width_interval(), expected);
            assert!(!machine.has_boxed_operand());
            let explicit = encoding
                .unary(source, destination)
                .build_raw(Bitvector32Term::Variable(Variable(985005)));
            assert_eq!(explicit.int64_width_interval(), expected);
        }
    }

    #[test]
    fn checking_cast_cache_survives_restore_but_not_a_new_verification() {
        use crate::kernel::{KernelMachineCastEncoding as E, KernelType};
        let mut term = KernelTerm::variable(
            KernelType::C(MachineIntegerType::Int32.c_type()),
            Variable(985003),
        );
        {
            let _session = crate::kernel::VerificationSession::enter();
            let snapshot = crate::kernel::VerificationSession::capture_state();
            for _ in 0..96 {
                term = KernelTerm::machine_cast_shared(
                    E::Generic,
                    MachineIntegerType::Int32,
                    MachineIntegerType::Int32,
                    term,
                );
            }
            let expected =
                term.checking_machine_cast(MachineIntegerType::Int32, MachineIntegerType::Int8);
            assert!(crate::kernel::VerificationSession::restore_state(&snapshot));
            crate::kernel::eval::begin_load_origin_epoch();
            let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
                term.checking_machine_cast(MachineIntegerType::Int32, MachineIntegerType::Int8)
            });
            assert_eq!(actual, expected);
            assert!(
                work <= 2,
                "restoring proof state rewalked the cast chain: {work}"
            );
        }
        let _session = crate::kernel::VerificationSession::enter();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            term.checking_machine_cast(MachineIntegerType::Int32, MachineIntegerType::Int8)
        });
        assert!(
            work >= 96,
            "another verification reused the previous cast cache: {work}"
        );
    }

    #[test]
    fn shared_cast_readings_match_boxed_readings_and_refusals() {
        use crate::kernel::{KernelMachineCastEncoding as E, machine_integer::FORMATS};
        let _session = crate::kernel::VerificationSession::enter();
        for source in FORMATS {
            for destination in FORMATS {
                let base = Bitvector32Term::Variable(Variable(985001));
                let inner = Bitvector32Term::MachineIntegerCast {
                    source: destination,
                    destination: source,
                    value: Box::new(base.clone()),
                };
                for operand in [
                    base,
                    inner,
                    source
                        .constant_term(
                            crate::kernel::MachineIntegerConstant::from_integer(
                                source.format(),
                                &1.into(),
                            )
                            .unwrap(),
                        )
                        .unwrap(),
                ] {
                    let boxed = Bitvector32Term::MachineIntegerCast {
                        source,
                        destination,
                        value: Box::new(operand),
                    };
                    let root = KernelTermImport::default()
                        .machine_arithmetic(destination, &boxed)
                        .unwrap();
                    assert_eq!(
                        MachineOperandView::Shared(&root).word32_constant(),
                        boxed.as_const()
                    );
                    assert_eq!(
                        MachineOperandView::Shared(&root).int64_constant(),
                        boxed.int64_as_const()
                    );
                    for observed in FORMATS {
                        let actual = shared_value_reading(observed, &root);
                        let expected = machine_value_reading(observed, &boxed);
                        assert_eq!(
                            actual.is_some(),
                            expected.is_some(),
                            "{observed:?}: {boxed:?}"
                        );
                        if let (Some((ty, term)), Some(expected)) = (actual, expected) {
                            let word = KernelTermExport::machine(&term).unwrap();
                            match expected {
                                ValueReading::Observation(expected_ty, expected) => {
                                    assert_eq!(ty, expected_ty);
                                    assert_eq!(&word, expected);
                                }
                                ValueReading::Constant(value) => assert_eq!(
                                    ty.constant_from_term(&word).unwrap().to_integer(),
                                    value
                                ),
                            }
                        }
                        assert_eq!(
                            MachineOperandView::Shared(&root).observe(observed),
                            IntegerTerm::from_machine(observed, boxed.clone()),
                            "observation {observed:?}: {boxed:?}"
                        );
                    }
                }
            }
        }
        let base = Bitvector32Term::Variable(Variable(985002));
        for op in [
            BitvectorUnaryOp::Int64From32,
            BitvectorUnaryOp::UInt64From32,
            BitvectorUnaryOp::UInt32From64,
            BitvectorUnaryOp::Int64FromUInt32,
            BitvectorUnaryOp::UInt64FromInt32,
            BitvectorUnaryOp::UInt64FromInt64,
        ] {
            let (encoding, source, destination) = E::of_unary(op).unwrap();
            let boxed = op.build_raw(base.clone());
            let root = KernelTermImport::default()
                .machine_arithmetic(destination, &boxed)
                .unwrap();
            assert_eq!(
                MachineOperandView::Shared(&root).cast().unwrap().0,
                encoding
            );
            assert_eq!(MachineOperandView::Shared(&root).cast().unwrap().1, source);
            for observed in FORMATS {
                assert_eq!(
                    MachineOperandView::Shared(&root).observe(observed),
                    IntegerTerm::from_machine(observed, boxed.clone())
                );
            }
        }
    }
}
