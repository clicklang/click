//! Keys project shared syntax without caching an enclosing native value tree.
//! Selected opaque leaves retain the existing native descriptor contract.
use super::*;
use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(in crate::kernel) enum BooleanStorageKey {
    Word(MachineTerm),
    Cast(MachineIntegerType, ConditionStorageKey),
}
impl BooleanStorageKey {
    pub(super) fn native(word: &MachineTerm) -> Self {
        match word {
            MachineTerm::BoolCast { to, value } => {
                Self::Cast(*to, ConditionStorageKey::native(value))
            }
            _ => Self::Word(word.clone()),
        }
    }
    pub(super) fn shared(root: &KernelTerm) -> Self {
        if root.ty() == &KernelType::Program(ProgramType::Bool) {
            return match root.node() {
                KernelTermNode::Variable(v) => Self::Word(MachineTerm::Variable(*v)),
                KernelTermNode::Legacy(value) => {
                    let PureFunctionArgument::Value(ProgramValue::Bool(word)) = value.value()
                    else {
                        unreachable!()
                    };
                    Self::native(word)
                }
                _ => unreachable!("raw Boolean carrier"),
            };
        }
        if let Some(value) = BooleanOperandView::Shared(root).constant() {
            Self::Word(MachineTerm::bool_cast(
                MachineIntegerType::UInt8,
                ConditionTerm::Constant(value),
            ))
        } else {
            Self::Cast(MachineIntegerType::UInt8, root.condition_storage_key())
        }
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
    If([ConditionStorageKey; 3]),
    Equal([ConditionStorageKey; 2]),
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
            _ => Self::native(&BooleanOperandView::Shared(root).identity_leaf()),
        }
    }
    fn native(term: &ConditionTerm) -> Self {
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
                ConditionTerm::PointerOffsetEqual(..) => 7,
                ConditionTerm::PointerEqual(..) => 8,
                ConditionTerm::PointerValueEqual(..) => 9,
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
                ConditionTerm::BoolLoad(..) => 19,
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
            match (&a.0.shape, &b.0.shape) {
                (ConditionShape::Atom(a), ConditionShape::Atom(b)) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                }
                (ConditionShape::If(a), ConditionShape::If(b)) => {
                    pending.extend(a.iter().zip(b).rev())
                }
                (ConditionShape::Equal(a), ConditionShape::Equal(b)) => {
                    pending.extend(a.iter().zip(b).rev())
                }
                _ => unreachable!("same condition key rank"),
            }
        }
        Ordering::Equal
    }
}

/// Native ProgramValue variant order. Numeric local keys live in the separate
/// machine-observation family; memory cells keep their native hash stream.
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
#[derive(Eq, PartialEq)]
pub(super) enum NativeStorageIdentity<'a> {
    Boolean(&'a BooleanStorageKey),
    Value(&'a ProgramValue),
}
impl NativeStorageIdentity<'_> {
    fn rank(&self) -> u8 {
        match self {
            Self::Boolean(_) => 2,
            Self::Value(v) => native_rank(v),
        }
    }
}
impl Hash for NativeStorageIdentity<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rank().hash(state);
        match self {
            Self::Boolean(v) => v.hash(state),
            Self::Value(v) => v.hash(state),
        }
    }
}
impl PartialOrd for NativeStorageIdentity<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for NativeStorageIdentity<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.rank()
            .cmp(&other.rank())
            .then_with(|| match (self, other) {
                (Self::Boolean(a), Self::Boolean(b)) => a.cmp(b),
                (Self::Value(a), Self::Value(b)) => a.cmp(b),
                _ => unreachable!("all Boolean storage keys use the projection"),
            })
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
                    ConditionShape::Atom(_) => {}
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
