//! Keys project shared syntax without caching an enclosing native value tree.
//! Selected opaque leaves retain the existing native descriptor contract.
use super::*;
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(in crate::kernel) struct BooleanStorageKey(BooleanKeyKind);

// Keep the word/cast split private: all BoolCast inputs are projected by the
// constructor, so a raw Word can never alias a projected Cast.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum BooleanKeyKind {
    Word(MachineTerm),
    Cast(MachineIntegerType, ConditionStorageKey),
}
impl BooleanStorageKey {
    pub(super) fn native(word: &MachineTerm) -> Self {
        Self(match word {
            MachineTerm::BoolCast { to, value } => {
                BooleanKeyKind::Cast(*to, ConditionStorageKey::native(value))
            }
            _ => BooleanKeyKind::Word(word.clone()),
        })
    }
    pub(super) fn shared(root: &KernelTerm) -> Self {
        if root.ty() == &KernelType::Program(ProgramType::Bool) {
            return match root.node() {
                KernelTermNode::Variable(v) => {
                    Self(BooleanKeyKind::Word(MachineTerm::Variable(*v)))
                }
                KernelTermNode::ImportedScalar(input) => Self::native(input.value()),
                KernelTermNode::ObservedArgument(_) | KernelTermNode::CallArgument(_) => {
                    let Some(PureFunctionArgument::Value(ProgramValue::Bool(word))) =
                        root.written_argument()
                    else {
                        unreachable!()
                    };
                    Self::native(word)
                }
                _ => unreachable!("raw Boolean carrier"),
            };
        }
        Self(
            if let Some(value) = BooleanOperandView::Shared(root).constant() {
                BooleanKeyKind::Word(MachineTerm::bool_cast(
                    MachineIntegerType::UInt8,
                    ConditionTerm::Constant(value),
                ))
            } else {
                BooleanKeyKind::Cast(MachineIntegerType::UInt8, root.condition_storage_key())
            },
        )
    }
}
impl PartialOrd for BooleanStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BooleanStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.0, &other.0) {
            (BooleanKeyKind::Word(a), BooleanKeyKind::Word(b)) => a.cmp(b),
            (BooleanKeyKind::Cast(at, a), BooleanKeyKind::Cast(bt, b)) => {
                at.cmp(bt).then_with(|| a.cmp(b))
            }
            (BooleanKeyKind::Word(a), BooleanKeyKind::Cast(..)) => {
                native_machine_rank(a).cmp(&BOOL_CAST_RANK)
            }
            (BooleanKeyKind::Cast(..), BooleanKeyKind::Word(b)) => {
                BOOL_CAST_RANK.cmp(&native_machine_rank(b))
            }
        }
    }
}

// Native MachineTerm variant order, shared by both family projections. The
// exhaustive match forces a review when a new opaque word variant is added.
const PURE_APPLICATION_RANK: u8 = 6;
const CLICK_APPLICATION_RANK: u8 = 7;
const FLOAT32_NEGATE_RANK: u8 = 13;
const FLOAT32_BINARY_RANK: u8 = 14;
const FLOAT64_NEGATE_RANK: u8 = 15;
const FLOAT64_BINARY_RANK: u8 = 16;
const BOOL_CAST_RANK: u8 = 17;
fn native_machine_rank(value: &MachineTerm) -> u8 {
    match value {
        MachineTerm::Constant { .. } => 0,
        MachineTerm::Variable(_) => 1,
        MachineTerm::Binary { .. } => 2,
        MachineTerm::Unary { .. } => 3,
        MachineTerm::If { .. } => 4,
        MachineTerm::RangeFold { .. } => 5,
        MachineTerm::PureFunctionApplication { .. } => PURE_APPLICATION_RANK,
        MachineTerm::ClickFunctionApplication { .. } => CLICK_APPLICATION_RANK,
        MachineTerm::AlgebraicMatch { .. } => 8,
        MachineTerm::MemoryLoad(..) => 9,
        MachineTerm::IntegerAddress(..) => 10,
        MachineTerm::IntegerToMachine { .. } => 11,
        MachineTerm::Cast { .. } => 12,
        MachineTerm::Float32Negate(_) => FLOAT32_NEGATE_RANK,
        MachineTerm::Float32Binary { .. } => FLOAT32_BINARY_RANK,
        MachineTerm::Float64Negate(_) => FLOAT64_NEGATE_RANK,
        MachineTerm::Float64Binary { .. } => FLOAT64_BINARY_RANK,
        MachineTerm::BoolCast { .. } => BOOL_CAST_RANK,
        MachineTerm::ThreadHandle(_) => 18,
    }
}

#[derive(Clone, Debug)]
pub(in crate::kernel) struct ConditionStorageKey(Arc<ConditionKeyData>);
#[derive(Debug, Hash)]
struct ConditionKeyData {
    shape: ConditionShape,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum ConditionShape {
    Atom(ConditionTerm),
    AlgebraicEqual([AlgebraicStorageKey; 2]),
    Compare(
        MachineIntegerType,
        CompareRelation,
        [ComparisonStorageOperand; 2],
    ),
    Overflows(MachineIntegerType, OverflowOperation, [ScalarStorageKey; 2]),
    Float(KernelFloatType, FloatPredicateKey),
    OffsetEqual([OffsetKey; 2]),
    AddressEqual([AddressKey; 2]),
    PointerEqual([PointerStorageKey; 2]),
    If([ConditionStorageKey; 3]),
    Equal([ConditionStorageKey; 2]),
}
#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum ComparisonStorageOperand {
    Term(ScalarStorageKey),
    Value(i128),
}

#[derive(Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum FloatPredicateKey {
    Comparison(ComparisonOperator, [ScalarStorageKey; 2]),
    Classification(FloatClassification, ScalarStorageKey),
}

impl FloatPredicateKey {
    fn native(value: &FloatCondition) -> Self {
        match value {
            FloatCondition::Comparison {
                operator,
                left,
                right,
            } => Self::Comparison(
                *operator,
                [
                    ScalarStorageKey::native(left),
                    ScalarStorageKey::native(right),
                ],
            ),
            FloatCondition::Classification {
                classification,
                value,
            } => Self::Classification(*classification, ScalarStorageKey::native(value)),
        }
    }
}

impl ComparisonStorageOperand {
    fn native(operand: crate::kernel::primitives::ComparisonSide<'_>) -> Self {
        use crate::kernel::primitives::ComparisonSide;
        match operand {
            ComparisonSide::Term(term) => Self::Term(ScalarStorageKey::native(term)),
            ComparisonSide::Value(value) => Self::Value(value),
        }
    }

    fn retained(operand: crate::kernel::machine_integer::comparison::FactOperand<'_>) -> Self {
        use crate::kernel::machine_integer::comparison::FactOperand;
        match operand {
            FactOperand::Term(MachineOperandView::Legacy(term)) => {
                Self::Term(ScalarStorageKey::native(term))
            }
            FactOperand::Term(MachineOperandView::Shared(root)) => {
                Self::Term(root.scalar_storage_key())
            }
            FactOperand::Value(value) => Self::Value(value),
        }
    }
}

impl ConditionStorageKey {
    fn new(shape: ConditionShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(ConditionKeyData {
            shape,
            fingerprint: hash.finish(),
        }))
    }
    pub(in crate::kernel) fn shared(root: &KernelTerm) -> Self {
        match root.node() {
            KernelTermNode::BoolIf { arguments } => Self::new(ConditionShape::If(
                arguments.each_ref().map(KernelTerm::condition_storage_key),
            )),
            KernelTermNode::BoolEqual { arguments } => Self::new(ConditionShape::Equal(
                arguments.each_ref().map(KernelTerm::condition_storage_key),
            )),
            KernelTermNode::AlgebraicEqual { arguments } => Self::new(
                ConditionShape::AlgebraicEqual(arguments.each_ref().map(algebraic_for_root)),
            ),
            KernelTermNode::BoolCompare {
                format,
                relation,
                arguments,
            } => {
                if let Some(native) = root.cached_condition_output() {
                    return Self::native(native);
                }
                use crate::kernel::machine_integer::comparison::stored_operand_identity;
                let operands = arguments.each_ref().map(|argument| {
                    argument.retained_machine_input().map_or(
                        MachineOperandView::Shared(argument),
                        MachineOperandView::Legacy,
                    )
                });
                let (format, operands) = stored_operand_identity(*format, *relation, operands);
                Self::new(ConditionShape::Compare(
                    format,
                    *relation,
                    operands.map(ComparisonStorageOperand::retained),
                ))
            }
            KernelTermNode::BoolOverflow {
                format,
                operation,
                arguments,
            } => Self::new(ConditionShape::Overflows(
                *format,
                *operation,
                arguments.each_ref().map(KernelTerm::scalar_storage_key),
            )),
            KernelTermNode::FloatCompare {
                format,
                operator,
                arguments,
            } => Self::new(ConditionShape::Float(
                *format,
                FloatPredicateKey::Comparison(
                    *operator,
                    arguments.each_ref().map(KernelTerm::scalar_storage_key),
                ),
            )),
            KernelTermNode::FloatClassify {
                format,
                classification,
                operand,
            } => Self::new(ConditionShape::Float(
                *format,
                FloatPredicateKey::Classification(*classification, operand.scalar_storage_key()),
            )),
            KernelTermNode::AddressOffsetEqual { arguments } => Self::new(
                ConditionShape::OffsetEqual(arguments.each_ref().map(offset_for_root)),
            ),
            KernelTermNode::AddressEqual { arguments } => Self::new(ConditionShape::AddressEqual(
                arguments.each_ref().map(AddressKey::shared),
            )),
            KernelTermNode::PointerEqual(pair) => Self::new(ConditionShape::PointerEqual(
                pair.arguments().each_ref().map(PointerStorageKey::shared),
            )),
            _ => Self::native(&BooleanOperandView::Shared(root).identity_leaf()),
        }
    }
    pub(in crate::kernel) fn native(term: &ConditionTerm) -> Self {
        enum Task<'a> {
            Enter(&'a ConditionTerm),
            If,
            Equal,
        }
        let mut pending = vec![Task::Enter(term)];
        let mut values = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Enter(ConditionTerm::BoolIf {
                    condition,
                    then_condition,
                    else_condition,
                }) => {
                    pending.push(Task::If);
                    pending.extend(
                        [else_condition, then_condition, condition].map(|v| Task::Enter(v)),
                    );
                }
                Task::Enter(ConditionTerm::BoolEqual(a, b)) => {
                    pending.push(Task::Equal);
                    pending.push(Task::Enter(b));
                    pending.push(Task::Enter(a));
                }
                Task::Enter(ConditionTerm::AlgebraicEqual(a, b)) => {
                    values.push(Self::new(ConditionShape::AlgebraicEqual([
                        AlgebraicStorageKey::native(a),
                        AlgebraicStorageKey::native(b),
                    ])))
                }
                Task::Enter(term @ ConditionTerm::Compare { .. }) => {
                    let (format, relation, left, right) =
                        term.comparison_fact().expect("comparison identity");
                    values.push(Self::new(ConditionShape::Compare(
                        format,
                        relation,
                        [left, right].map(ComparisonStorageOperand::native),
                    )));
                }
                Task::Enter(ConditionTerm::Overflows {
                    format,
                    op,
                    left,
                    right,
                }) => {
                    values.push(Self::new(ConditionShape::Overflows(
                        *format,
                        *op,
                        [
                            ScalarStorageKey::native(left),
                            ScalarStorageKey::native(right),
                        ],
                    )));
                }
                Task::Enter(ConditionTerm::Float32(value)) => {
                    values.push(Self::new(ConditionShape::Float(
                        KernelFloatType::Float32,
                        FloatPredicateKey::native(value),
                    )))
                }
                Task::Enter(ConditionTerm::Float64(value)) => {
                    values.push(Self::new(ConditionShape::Float(
                        KernelFloatType::Float64,
                        FloatPredicateKey::native(value),
                    )))
                }
                Task::Enter(ConditionTerm::AddressOffsetEqual(a, b)) => {
                    values.push(Self::new(ConditionShape::OffsetEqual([
                        OffsetKey::native(a),
                        OffsetKey::native(b),
                    ])))
                }
                Task::Enter(ConditionTerm::AddressEqual(a, b)) => {
                    values.push(Self::new(ConditionShape::AddressEqual([
                        AddressKey::native(a),
                        AddressKey::native(b),
                    ])))
                }
                Task::Enter(ConditionTerm::PointerEqual(a, b)) => {
                    values.push(Self::new(ConditionShape::PointerEqual([
                        PointerStorageKey::native(a),
                        PointerStorageKey::native(b),
                    ])))
                }
                Task::Enter(term) => values.push(Self::new(ConditionShape::Atom(term.clone()))),
                Task::If => {
                    let no = values.pop().unwrap();
                    let yes = values.pop().unwrap();
                    let guard = values.pop().unwrap();
                    values.push(Self::new(ConditionShape::If([guard, yes, no])));
                }
                Task::Equal => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::new(ConditionShape::Equal([a, b])));
                }
            }
        }
        values.pop().expect("condition key")
    }
}
impl ConditionShape {
    fn rank(&self) -> u8 {
        match self {
            Self::AlgebraicEqual(_) => 2,
            Self::Compare(..) => 3,
            Self::Overflows(..) => 4,
            Self::Float(KernelFloatType::Float32, _) => 5,
            Self::Float(KernelFloatType::Float64, _) => 6,
            Self::OffsetEqual(_) => 7,
            Self::AddressEqual(_) => 8,
            Self::PointerEqual(_) => 9,
            Self::If(_) => 17,
            Self::Equal(_) => 18,
            Self::Atom(value) => match value {
                ConditionTerm::Constant(_) => 0,
                ConditionTerm::Variable(_) => 1,
                ConditionTerm::AlgebraicEqual(..) => 2,
                ConditionTerm::Compare { .. } => 3,
                ConditionTerm::Overflows { .. } => 4,
                ConditionTerm::Float32(_) => 5,
                ConditionTerm::Float64(_) => 6,
                ConditionTerm::AddressOffsetEqual(..) => 7,
                ConditionTerm::AddressEqual(..) => 8,
                ConditionTerm::PointerEqual(..) => 9,
                ConditionTerm::IntegerLessThan(..) => 10,
                ConditionTerm::IntegerLessEqual(..) => 11,
                ConditionTerm::IntegerGreaterThan(..) => 12,
                ConditionTerm::IntegerGreaterEqual(..) => 13,
                ConditionTerm::IntegerEqual(..) => 14,
                ConditionTerm::IntegerNotEqual(..) => 15,
                ConditionTerm::BoolApplication(_) => 16,
                ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
                    unreachable!("projected connective")
                }
            },
        }
    }
}
impl Hash for ConditionStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl PartialEq for ConditionStorageKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for ConditionStorageKey {}
impl PartialOrd for ConditionStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ConditionStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            if Arc::ptr_eq(&a.0, &b.0) || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let order = a.0.shape.rank().cmp(&b.0.shape.rank());
            if !order.is_eq() {
                return order;
            }
            let order = match (&a.0.shape, &b.0.shape) {
                (ConditionShape::Atom(a), ConditionShape::Atom(b)) => a.cmp(b),
                (ConditionShape::AlgebraicEqual(a), ConditionShape::AlgebraicEqual(b)) => a.cmp(b),
                (ConditionShape::Compare(af, ar, a), ConditionShape::Compare(bf, br, b)) => {
                    (af, ar, a).cmp(&(bf, br, b))
                }
                (ConditionShape::Overflows(af, ao, a), ConditionShape::Overflows(bf, bo, b)) => {
                    (af, ao, a).cmp(&(bf, bo, b))
                }
                (ConditionShape::Float(_, a), ConditionShape::Float(_, b)) => a.cmp(b),
                (ConditionShape::OffsetEqual(a), ConditionShape::OffsetEqual(b)) => a.cmp(b),
                (ConditionShape::AddressEqual(a), ConditionShape::AddressEqual(b)) => a.cmp(b),
                (ConditionShape::PointerEqual(a), ConditionShape::PointerEqual(b)) => a.cmp(b),
                (ConditionShape::If(a), ConditionShape::If(b)) => {
                    pending.extend(a.iter().zip(b).rev());
                    Ordering::Equal
                }
                (ConditionShape::Equal(a), ConditionShape::Equal(b)) => {
                    pending.extend(a.iter().zip(b).rev());
                    Ordering::Equal
                }
                _ => unreachable!("same condition key rank"),
            };
            if !order.is_eq() {
                return order;
            }
        }
        Ordering::Equal
    }
}

/// Exact program value identity for descriptor storage and typed call arguments.
/// Local numeric observations use a different key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum ProgramStorageKey {
    Scalar(ProgramType, ScalarStorageKey),
    Boolean(BooleanStorageKey),
    Pointer(PointerStorageKey),
    Algebraic(AlgebraicStorageKey),
    Native(ProgramValue),
}

impl ProgramStorageKey {
    pub(in crate::kernel) fn for_value(value: &ExecutionValue) -> Self {
        match value {
            ExecutionValue::Native(value) => Self::native(value),
            ExecutionValue::Shared(root) => {
                // The execution handoff borrows the call's written carrier.
                // Nested call arguments instead follow structural export.
                if matches!(root.node(), KernelTermNode::Call { .. })
                    && MachineIntegerType::from_program_type(value.program_type()).is_some()
                {
                    let word = root.machine_conversion_leaf().expect("machine result call");
                    return Self::Scalar(value.program_type(), ScalarStorageKey::native(word));
                }
                Self::shared(root)
            }
        }
    }

    pub(in crate::kernel) fn native(value: &ProgramValue) -> Self {
        match value {
            crate::kernel::integer_c_value!(word)
            | ProgramValue::Float32(word)
            | ProgramValue::Float64(word) => {
                Self::Scalar(value.program_type(), ScalarStorageKey::native(word))
            }
            ProgramValue::Bool(word) => Self::Boolean(BooleanStorageKey::native(word)),
            ProgramValue::Pointer(pointer) => Self::Pointer(PointerStorageKey::native(pointer)),
            ProgramValue::Parameter(value) => Self::Algebraic(AlgebraicStorageKey::native(value)),
            ProgramValue::PointerInteger(_) | ProgramValue::Void => Self::Native(value.clone()),
        }
    }

    pub(super) fn shared(root: &KernelTerm) -> Self {
        if let Some(PureFunctionArgument::Value(value)) = root.written_argument() {
            return Self::native(value);
        }
        if root.pointer_payload().is_some() {
            return Self::Pointer(pointer_for_root(root));
        }
        match (root.ty(), root.node()) {
            (KernelType::Algebraic(_), _) => Self::Algebraic(algebraic_for_root(root)),
            (_, KernelTermNode::ProgramParameter { operand }) => {
                Self::Algebraic(algebraic_for_root(operand))
            }
            (KernelType::Bool | KernelType::Program(ProgramType::Bool), _) => {
                Self::Boolean(BooleanStorageKey::shared(root))
            }
            (KernelType::Program(ty), KernelTermNode::ImportedScalar(input)) => {
                debug_assert_ne!(*ty, ProgramType::Bool);
                Self::Scalar(input.carrier(), root.scalar_storage_key())
            }
            (KernelType::Program(ty), _)
                if MachineIntegerType::from_program_type(*ty).is_some()
                    || KernelFloatType::from_program_type(*ty).is_some() =>
            {
                Self::Scalar(*ty, root.scalar_storage_key())
            }
            _ => Self::native(
                root.program_value_native_compat()
                    .expect("program storage key"),
            ),
        }
    }

    fn rank(&self) -> u8 {
        match self {
            Self::Boolean(_) => 2,
            Self::Pointer(_) => 15,
            Self::Algebraic(_) => 16,
            Self::Scalar(ty, _) => match ty {
                ProgramType::Int8 => 3,
                ProgramType::Int16 => 4,
                ProgramType::Int32 => 5,
                ProgramType::UInt8 => 6,
                ProgramType::UInt16 => 7,
                ProgramType::UInt32 => 8,
                ProgramType::Int64 => 9,
                ProgramType::UInt64 => 10,
                ProgramType::Int128 => 11,
                ProgramType::UInt128 => 12,
                ProgramType::Float32 => 13,
                ProgramType::Float64 => 14,
                _ => unreachable!("scalar program carrier"),
            },
            Self::Native(value) => native_rank(value),
        }
    }
}

impl Hash for ProgramStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rank().hash(state);
        match self {
            Self::Scalar(_, key) => key.hash(state),
            Self::Boolean(key) => key.hash(state),
            Self::Pointer(key) => key.hash(state),
            Self::Algebraic(key) => key.hash(state),
            Self::Native(value) => value.hash(state),
        }
    }
}

impl PartialOrd for ProgramStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ProgramStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank()
            .cmp(&other.rank())
            .then_with(|| match (self, other) {
                (Self::Scalar(_, a), Self::Scalar(_, b)) => a.cmp(b),
                (Self::Boolean(a), Self::Boolean(b)) => a.cmp(b),
                (Self::Pointer(a), Self::Pointer(b)) => a.cmp(b),
                (Self::Algebraic(a), Self::Algebraic(b)) => a.cmp(b),
                (Self::Native(a), Self::Native(b)) => a.cmp(b),
                _ => unreachable!("same program value rank"),
            })
    }
}

/// Native ProgramValue variant order. Numeric local keys live in the separate
/// machine-observation family; numeric memory cells keep native structural keys.
fn native_rank(value: &ProgramValue) -> u8 {
    match value {
        ProgramValue::PointerInteger(_) => 0,
        ProgramValue::Void => 1,
        ProgramValue::Bool(_) => 2,
        ProgramValue::Int8(_) => 3,
        ProgramValue::Int16(_) => 4,
        ProgramValue::Int32(_) => 5,
        ProgramValue::UInt8(_) => 6,
        ProgramValue::UInt16(_) => 7,
        ProgramValue::UInt32(_) => 8,
        ProgramValue::Int64(_) => 9,
        ProgramValue::UInt64(_) => 10,
        ProgramValue::Int128(_) => 11,
        ProgramValue::UInt128(_) => 12,
        ProgramValue::Float32(_) => 13,
        ProgramValue::Float64(_) => 14,
        ProgramValue::Pointer(_) => 15,
        ProgramValue::Parameter(_) => 16,
    }
}
impl Drop for ConditionStorageKey {
    fn drop(&mut self) {
        fn take(key: &mut ConditionStorageKey, pending: &mut Vec<ConditionStorageKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0) {
                match std::mem::replace(
                    &mut data.shape,
                    ConditionShape::Atom(ConditionTerm::Constant(false)),
                ) {
                    ConditionShape::If(children) => pending.extend(children),
                    ConditionShape::Equal(children) => pending.extend(children),
                    ConditionShape::Atom(_)
                    | ConditionShape::AlgebraicEqual(_)
                    | ConditionShape::Compare(..)
                    | ConditionShape::Overflows(..)
                    | ConditionShape::Float(..)
                    | ConditionShape::OffsetEqual(_)
                    | ConditionShape::AddressEqual(_)
                    | ConditionShape::PointerEqual(_) => {}
                }
            }
        }
        let mut pending = Vec::new();
        take(self, &mut pending);
        while let Some(mut child) = pending.pop() {
            take(&mut child, &mut pending);
        }
    }
}

mod pointer;
pub(in crate::kernel) use pointer::for_root as pointer_for_root;
pub(in crate::kernel) use pointer::{AddressKey, OffsetKey, PointerStorageKey, offset_for_root};

mod algebraic;
pub(in crate::kernel) use algebraic::AlgebraicStorageKey;
pub(in crate::kernel) use algebraic::for_root as algebraic_for_root;

mod scalar;
pub(in crate::kernel) use scalar::ScalarStorageKey;

thread_local! {
    // Syntax is immutable across state restores, but a fresh verification must
    // pay for its own selected key construction regardless of earlier runs.
    static CONDITION_KEYS: std::cell::RefCell<crate::id_hash::U64Map<ConditionStorageKey>> = Default::default();
}
pub(in crate::kernel) fn clear_session_key_memos() {
    CONDITION_KEYS.with(|keys| keys.borrow_mut().clear());
    scalar::clear_session_key_memos();
    algebraic::clear_session_key_memos();
    pointer::clear_session_key_memos();
}
pub(in crate::kernel) fn condition_for_root(source: &KernelTerm) -> ConditionStorageKey {
    CONDITION_KEYS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(&root.id()) {
                continue;
            }
            if !finish {
                match root.node() {
                    KernelTermNode::BoolIf { arguments } => {
                        pending.push((root, true));
                        pending.extend(arguments.iter().rev().map(|child| (child, false)));
                        continue;
                    }
                    KernelTermNode::BoolEqual { arguments } => {
                        pending.push((root, true));
                        pending.extend(arguments.iter().rev().map(|child| (child, false)));
                        continue;
                    }
                    _ => {}
                }
            }
            let key = ConditionStorageKey::shared(root);
            keys.borrow_mut().insert(root.id(), key);
        }
        keys.borrow()
            .get(&source.id())
            .expect("condition storage key")
            .clone()
    })
}

pub(in crate::kernel) fn scalar_for_root(root: &KernelTerm) -> ScalarStorageKey {
    scalar::for_root(root)
}
