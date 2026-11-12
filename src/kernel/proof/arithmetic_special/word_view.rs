//! Borrowed nodes for the bounded tagged-address certificate evaluator.
use super::*;
use crate::kernel::MachineOperandView as View;

#[derive(Clone, Copy)]
pub(super) struct Word<'a>(pub(super) View<'a>);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Key {
    Native(usize),
    Shared(u64),
}
pub(super) enum Node<'a> {
    PointerAddress(&'a Pointer),
    Binary {
        format: MachineIntegerType,
        op: MachineBinaryOp,
        left: Word<'a>,
        right: Word<'a>,
    },
    Other,
}
impl<'a> Word<'a> {
    pub(super) fn key(self) -> Key {
        match self.0 {
            View::Legacy(value) => Key::Native(value as *const _ as usize),
            View::Shared(root) => Key::Shared(root.id()),
        }
    }
    pub(super) fn leaf(self) -> Option<&'a MachineTerm> {
        match self.0 {
            View::Legacy(value) => Some(value),
            View::Shared(root) => root
                .machine_conversion_leaf()
                .or_else(|| root.machine_read_leaf()),
        }
    }
    pub(super) fn node(self) -> Node<'a> {
        if let Some((format, op, [left, right])) = self.0.binary() {
            return Node::Binary {
                format,
                op,
                left: Word(left),
                right: Word(right),
            };
        }
        if let Some(MachineTerm::PointerAddress(pointer, _)) = self.leaf() {
            return Node::PointerAddress(pointer);
        }
        Node::Other
    }
    pub(super) fn uint64_as_const(self) -> Option<u64> {
        self.0.uint64_constant()
    }
}
impl<'a> From<&'a MachineTerm> for Word<'a> {
    fn from(value: &'a MachineTerm) -> Self {
        Self(View::Legacy(value))
    }
}

pub(super) fn equal(left: Word<'_>, right: Word<'_>) -> bool {
    operand_identity::equal(left.0, right.0)
}
pub(super) fn charge(word: Word<'_>) -> bool {
    pointer_index_payload(word.0).is_some_and(charge_payload)
}

// The same supported shape and hash as the native certificate, memoized by
// immediate node identity. Hashes only filter candidates; equal checks them.
pub(super) fn hashes(roots: &[Word<'_>]) -> Option<HashMap<Key, u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut values: HashMap<Key, u64> = HashMap::new();
    while let Some((word, finish)) = pending.pop() {
        if values.contains_key(&word.key()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        match word.node() {
            Node::Binary {
                format,
                op,
                left,
                right,
            } if matches!(
                (format, op),
                (
                    MachineIntegerType::Int32 | MachineIntegerType::UInt64,
                    MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr
                )
            ) =>
            {
                if !finish {
                    pending.extend([(word, true), (right, false), (left, false)]);
                    continue;
                }
                let header = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(MachineTerm::constant(0)),
                    right: Box::new(MachineTerm::constant(0)),
                };
                let mut hash = DefaultHasher::new();
                std::mem::discriminant(&header).hash(&mut hash);
                (format, op).hash(&mut hash);
                values.get(&left.key())?.hash(&mut hash);
                values.get(&right.key())?.hash(&mut hash);
                values.insert(word.key(), hash.finish());
            }
            _ => {
                let leaf = word
                    .0
                    .literal()
                    .map(std::borrow::Cow::Owned)
                    .or_else(|| word.0.read_source())?;
                values.insert(word.key(), bounded_term_hash(&leaf)?);
            }
        }
    }
    Some(values)
}

pub(super) fn constants(roots: &[Word<'_>]) -> HashMap<Key, Option<u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut values = HashMap::new();
    while let Some((word, finish)) = pending.pop() {
        if values.contains_key(&word.key()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return HashMap::new();
        }
        let value = if let Some(value) = word.uint64_as_const() {
            Some(value)
        } else if let Some((MachineIntegerType::UInt64, op, [left, right])) = word.0.binary() {
            let (left, right) = (Word(left), Word(right));
            if !finish {
                pending.extend([(word, true), (right, false), (left, false)]);
                continue;
            }
            values
                .get(&left.key())
                .copied()
                .flatten()
                .zip(values.get(&right.key()).copied().flatten())
                .and_then(|(left, right): (u64, u64)| {
                    use MachineBinaryOp::*;
                    match op {
                        Add => Some(left.wrapping_add(right)),
                        Subtract => Some(left.wrapping_sub(right)),
                        Multiply => Some(left.wrapping_mul(right)),
                        Divide if right != 0 => Some(left / right),
                        Remainder if right != 0 => Some(left % right),
                        ShiftLeft if right < 64 => Some(left.wrapping_shl(right as u32)),
                        ShiftRight if right < 64 => Some(left >> right),
                        BitwiseAnd => Some(left & right),
                        BitwiseOr => Some(left | right),
                        BitwiseXor => Some(left ^ right),
                        _ => None,
                    }
                })
        } else if let Some((MachineIntegerType::UInt64, MachineUnaryOp::BitwiseNot, operand)) =
            word.0.unary()
        {
            let operand = Word(operand);
            if !finish {
                pending.extend([(word, true), (operand, false)]);
                continue;
            }
            values
                .get(&operand.key())
                .copied()
                .flatten()
                .map(|value: u64| !value)
        } else if let Some((encoding, _, _, operand)) = word.0.cast() {
            use MachineCastSpelling::*;
            if matches!(encoding, UInt64From32 | UInt64FromInt32 | UInt64FromInt64) {
                let direct = match encoding {
                    UInt64From32 => operand.word32_constant().map(u64::from),
                    UInt64FromInt32 => operand.word32_constant().map(|v| v as i32 as i64 as u64),
                    UInt64FromInt64 => operand.int64_constant().map(|v| v as u64),
                    _ => None,
                };
                if direct.is_some() {
                    direct
                } else {
                    let operand = Word(operand);
                    if !finish {
                        pending.extend([(word, true), (operand, false)]);
                        continue;
                    }
                    values.get(&operand.key()).copied().flatten()
                }
            } else {
                None
            }
        } else {
            None
        };
        values.insert(word.key(), value);
    }
    values
}

impl std::fmt::Debug for Word<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.key().fmt(f)
    }
}
