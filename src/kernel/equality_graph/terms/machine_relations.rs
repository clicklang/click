//! Cross-format relations between machine operators and conversions
//! (`design/machine-integers.md`, Decisions, 2026-10-29, "Every format its
//! own nodes").
//!
//! A conversion and an operator meet in the e-graph as nodes of their own
//! formats, and three rules relate them where they meet:
//!
//! - **R-dist.** For a conversion `C` to a format no wider than its source,
//!   `C(a op b) == C(a) op C(b)` for the sign-free operators `+ - * & | ^`,
//!   `C(~a) == ~C(a)`, and `C(a << k) == C(a) << k` for a constant count `k`
//!   below the destination's width. Sign-free operators compute modulo
//!   `2^w`, and reduction to fewer bits is a ring homomorphism that commutes
//!   with the bitwise operators bit by bit, so the destination's operator
//!   over the converted operands has the converted value.
//! - **R-comp.** A conversion of a conversion is one conversion
//!   `Cast(S -> D, x)` when the inner one preserves its operand's value and
//!   the outer reads exactly the inner's format, or when the outer keeps no
//!   more bits than the intermediate and the source has a full-width carrier.
//!   For narrow source carriers, it must also keep no more bits than the
//!   source. Every conversion keeps its operand's low bits, and a
//!   value-preserving one keeps the value.
//! - **R0.** A conversion between the signed and unsigned formats of one
//!   width is a bijection: the conversion back of its result is in its
//!   operand's class, so equality carries across it by congruence. An 8- or
//!   16-bit value is native, a value of its own width, so R0 and R-comp
//!   apply at every width.
//!
//! Each rule fires where a conversion node and an operator or conversion
//! node meet in one class: when either is interned, and when a union brings
//! them together. Every class keeps at most one operator per format and
//! operator, one conversion per kind applied to it, and one conversion per
//! kind it holds, so a firing interns at most three nodes and one union, a
//! union fires a bounded number of pairs, and each pair fires once.
//!
//! The 32-bit operators are word operators while the term arena files a
//! `uint32` operation at `int32` (rule K1), so they read either 32-bit
//! format here; σ at 32 bits is peeled before the e-graph sees it (K1). A
//! narrow widening into 32 bits is a node of its own width, linked to its
//! operand by value (K8, a relation across widths). The rules act on the
//! 64-bit conversions (`UInt64FromInt64`, the low word, the extensions), on
//! conversions into and between 8 and 16 bits, on narrow widenings, and on
//! conversions involving 128-bit intermediates; they reach σ at 32 bits once
//! it is a node (step 4b).

use super::*;
use crate::kernel::machine_integer::representation;
use crate::kernel::{BitvectorBinaryOp as B, BitvectorUnaryOp as U, MachineUnaryOp};

/// The format an operator node computes in: the 32-bit word (rule K1), or
/// one format.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum OperatorFormat {
    Word32,
    Format(MachineIntegerType),
}

impl OperatorFormat {
    fn of(format: MachineIntegerType) -> Self {
        if format.format().bits() == 32 {
            Self::Word32
        } else {
            Self::Format(format)
        }
    }
}

/// A sign-free operator: its result's low bits depend only on its
/// operands' low bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum SignFree {
    Add,
    Subtract,
    Multiply,
    And,
    Or,
    Xor,
    ShiftLeft,
    Not,
}

impl SignFree {
    fn of(op: MachineBinaryOp) -> Option<Self> {
        Some(match op {
            MachineBinaryOp::Add => Self::Add,
            MachineBinaryOp::Subtract => Self::Subtract,
            MachineBinaryOp::Multiply => Self::Multiply,
            MachineBinaryOp::BitwiseAnd => Self::And,
            MachineBinaryOp::BitwiseOr => Self::Or,
            MachineBinaryOp::BitwiseXor => Self::Xor,
            MachineBinaryOp::ShiftLeft => Self::ShiftLeft,
            MachineBinaryOp::Divide | MachineBinaryOp::Remainder | MachineBinaryOp::ShiftRight => {
                return None;
            }
        })
    }

    fn binary(self) -> Option<MachineBinaryOp> {
        Some(match self {
            Self::Add => MachineBinaryOp::Add,
            Self::Subtract => MachineBinaryOp::Subtract,
            Self::Multiply => MachineBinaryOp::Multiply,
            Self::And => MachineBinaryOp::BitwiseAnd,
            Self::Or => MachineBinaryOp::BitwiseOr,
            Self::Xor => MachineBinaryOp::BitwiseXor,
            Self::ShiftLeft => MachineBinaryOp::ShiftLeft,
            Self::Not => return None,
        })
    }
}

/// What a conversion reads: one format, or the 64-bit word of either
/// signedness (`UInt32From64`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum CastSource {
    Word64,
    Format(MachineIntegerType),
}

impl CastSource {
    fn bits(self) -> u32 {
        match self {
            Self::Word64 => 64,
            Self::Format(format) => format.format().bits(),
        }
    }

    /// Whether an operator of `format` computes the bits this conversion
    /// reads.
    fn reads_operator(self, format: OperatorFormat) -> bool {
        match (self, format) {
            (Self::Format(source), OperatorFormat::Word32) => source.format().bits() == 32,
            (Self::Format(source), OperatorFormat::Format(format)) => source == format,
            (Self::Word64, OperatorFormat::Format(format)) => format.format().bits() == 64,
            (Self::Word64, OperatorFormat::Word32) => false,
        }
    }

    /// Whether this conversion reads a value of `format` as that value,
    /// with no change of width or signedness. A 32-bit format also reads
    /// the other 32-bit format's word only through σ, which is not exact.
    fn reads_exactly(self, format: MachineIntegerType) -> bool {
        match self {
            Self::Format(source) => source == format,
            Self::Word64 => false,
        }
    }
}

/// A conversion's kind: what it reads and the format it produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct CastKey {
    source: CastSource,
    destination: MachineIntegerType,
}

impl CastKey {
    fn truncates(self) -> bool {
        self.destination.format().bits() <= self.source.bits()
    }

    /// Whether the conversion keeps its operand's value: a widening into a
    /// format that contains the source.
    fn preserves_value(self) -> bool {
        match self.source {
            CastSource::Format(source) => self.destination.format().contains(source.format()),
            CastSource::Word64 => false,
        }
    }
}

/// A machine operator or conversion head, by node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum MachineHead {
    Unary(U),
    Binary(B),
}

/// A relation queued to fire between two nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Relation {
    Distribute,
    Compose,
    Invert,
}

/// A machine application, read structurally: its operand IDs are the ones
/// it was interned with.
enum Decoded {
    Operator {
        format: OperatorFormat,
        op: SignFree,
        left: u64,
        right: Option<u64>,
    },
    Cast {
        key: CastKey,
        operand: u64,
    },
}

fn cast_key_of_unary(op: U) -> Option<CastKey> {
    use MachineIntegerType as Ty;
    let (source, destination) = match op {
        U::MachineIntegerCast {
            source,
            destination,
        } => (CastSource::Format(source), destination),
        U::UInt32From64 => (CastSource::Word64, Ty::UInt32),
        U::UInt64FromInt64 => (CastSource::Format(Ty::Int64), Ty::UInt64),
        U::Int64From32 => (CastSource::Format(Ty::Int32), Ty::Int64),
        U::UInt64From32 => (CastSource::Format(Ty::UInt32), Ty::UInt64),
        U::Int64FromUInt32 => (CastSource::Format(Ty::UInt32), Ty::Int64),
        U::UInt64FromInt32 => (CastSource::Format(Ty::Int32), Ty::UInt64),
        U::Machine(..) | U::Float32Negate | U::Float64Negate => return None,
    };
    Some(CastKey {
        source,
        destination,
    })
}

impl TermClasses {
    /// Records the head a machine operator or conversion node names, so an
    /// application of it can be read back.
    pub(super) fn retain_machine_head(&mut self, id: u64, node: &Node) {
        let head = match node {
            Node::MachineUnary(op, _) => MachineHead::Unary(*op),
            Node::MachineBinary(op, _) => MachineHead::Binary(*op),
            _ => return,
        };
        self.machine_heads.insert(id, head);
    }

    fn decode_machine(&self, id: u64) -> Option<Decoded> {
        let operator = |format, op, left, right| {
            Some(Decoded::Operator {
                format,
                op,
                left,
                right,
            })
        };
        match *self.applications.get(&id)? {
            Application::Int32Add(left, right) => {
                operator(OperatorFormat::Word32, SignFree::Add, left, Some(right))
            }
            Application::Int32Binary(Int32Binary::BitwiseXor, left, right) => {
                operator(OperatorFormat::Word32, SignFree::Xor, left, Some(right))
            }
            Application::Int32Binary(Int32Binary::Other(B::Machine(format, op)), left, right)
                if format.format().bits() == 32 =>
            {
                operator(OperatorFormat::Word32, SignFree::of(op)?, left, Some(right))
            }
            Application::Int32Unary(Int32Unary::Not, value) => {
                operator(OperatorFormat::Word32, SignFree::Not, value, None)
            }
            Application::Int32Unary(Int32Unary::Cast(source, destination), operand) => {
                Some(Decoded::Cast {
                    key: CastKey {
                        source: CastSource::Format(source),
                        destination,
                    },
                    operand,
                })
            }
            Application::UInt64Binary(op, left, right) => {
                let op = match op {
                    UInt64Binary::Add => SignFree::Add,
                    UInt64Binary::Subtract => SignFree::Subtract,
                    UInt64Binary::Multiply => SignFree::Multiply,
                    UInt64Binary::And => SignFree::And,
                    UInt64Binary::Or => SignFree::Or,
                    UInt64Binary::Xor => SignFree::Xor,
                    UInt64Binary::Divide | UInt64Binary::Remainder => return None,
                };
                operator(
                    OperatorFormat::Format(MachineIntegerType::UInt64),
                    op,
                    left,
                    Some(right),
                )
            }
            Application::Apply(function, argument) => {
                if let Some(head) = self.machine_heads.get(&function) {
                    return match *head {
                        MachineHead::Unary(U::Machine(format, MachineUnaryOp::BitwiseNot)) => {
                            operator(OperatorFormat::of(format), SignFree::Not, argument, None)
                        }
                        MachineHead::Unary(op) => Some(Decoded::Cast {
                            key: cast_key_of_unary(op)?,
                            operand: argument,
                        }),
                        MachineHead::Binary(_) => None,
                    };
                }
                let Some(Application::Apply(head, left)) =
                    self.applications.get(&function).copied()
                else {
                    return None;
                };
                let Some(MachineHead::Binary(B::Machine(format, op))) =
                    self.machine_heads.get(&head).copied()
                else {
                    return None;
                };
                // A 64-bit shift's count is an opaque argument, not a word.
                let op = SignFree::of(op)
                    .filter(|op| *op != SignFree::ShiftLeft || format.format().bits() <= 32)?;
                operator(OperatorFormat::of(format), op, left, Some(argument))
            }
            _ => None,
        }
    }

    /// Indexes `id` if it is a machine operator or conversion, and fires the
    /// relations it meets. Called whenever the application is (re)indexed.
    pub(super) fn relate_machine_application(&mut self, id: u64) {
        let Some(decoded) = self.decode_machine(id) else {
            return;
        };
        match decoded {
            Decoded::Operator { format, op, .. } => {
                let class = self.root(id);
                let mut operators = self
                    .class_operators
                    .get(&class)
                    .cloned()
                    .unwrap_or_default();
                if operators.contains_key(&(format, op)) {
                    return;
                }
                operators.insert((format, op), id);
                self.class_operators.insert(class, operators);
                for (_, cast) in self
                    .casts_of_class
                    .get(&class)
                    .cloned()
                    .unwrap_or_default()
                    .iter()
                {
                    self.queue_machine_relation(Relation::Distribute, *cast, id);
                }
            }
            Decoded::Cast { key, operand } => {
                let operand = self.root(operand);
                let mut casts = self
                    .casts_of_class
                    .get(&operand)
                    .cloned()
                    .unwrap_or_default();
                if !casts.contains_key(&key) {
                    casts.insert(key, id);
                    self.casts_of_class.insert(operand, casts);
                }
                for (_, operator) in self
                    .class_operators
                    .get(&operand)
                    .cloned()
                    .unwrap_or_default()
                    .iter()
                {
                    self.queue_machine_relation(Relation::Distribute, id, *operator);
                }
                for (_, inner) in self
                    .class_casts
                    .get(&operand)
                    .cloned()
                    .unwrap_or_default()
                    .iter()
                {
                    self.queue_machine_relation(Relation::Compose, id, *inner);
                }
                let class = self.root(id);
                let mut members = self.class_casts.get(&class).cloned().unwrap_or_default();
                if !members.contains_key(&key) {
                    members.insert(key, id);
                    self.class_casts.insert(class, members);
                }
                for (_, outer) in self
                    .casts_of_class
                    .get(&class)
                    .cloned()
                    .unwrap_or_default()
                    .iter()
                {
                    self.queue_machine_relation(Relation::Compose, *outer, id);
                }
                self.queue_machine_relation(Relation::Invert, id, operand);
            }
        }
    }

    /// Moves the machine relation indexes of `moved` into `kept`, firing the
    /// pairs the union brings together: a conversion of `kept` with an
    /// operator or conversion `moved` holds. The conversions of `moved` are
    /// its uses, which the union reindexes.
    pub(super) fn merge_machine_relations(&mut self, moved: u64, kept: u64) {
        let outer = self.casts_of_class.get(&kept).cloned().unwrap_or_default();
        if let Some(operators) = self.class_operators.get(&moved).cloned() {
            self.class_operators.remove(&moved);
            let mut kept_operators = self.class_operators.get(&kept).cloned().unwrap_or_default();
            for (key, operator) in operators.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if kept_operators.contains_key(key) {
                    continue;
                }
                kept_operators.insert(*key, *operator);
                for (_, cast) in outer.iter() {
                    self.queue_machine_relation(Relation::Distribute, *cast, *operator);
                }
            }
            self.class_operators.insert(kept, kept_operators);
        }
        if let Some(members) = self.class_casts.get(&moved).cloned() {
            self.class_casts.remove(&moved);
            let mut kept_members = self.class_casts.get(&kept).cloned().unwrap_or_default();
            for (key, inner) in members.iter() {
                crate::instrumentation::record_deterministic_work(1);
                if kept_members.contains_key(key) {
                    continue;
                }
                kept_members.insert(*key, *inner);
                for (_, cast) in outer.iter() {
                    self.queue_machine_relation(Relation::Compose, *cast, *inner);
                }
            }
            self.class_casts.insert(kept, kept_members);
        }
        self.casts_of_class.remove(&moved);
    }

    fn queue_machine_relation(&mut self, relation: Relation, first: u64, second: u64) {
        let key = match relation {
            Relation::Invert => (first, first),
            _ => (first, second),
        };
        if !self.fired_machine_relations.contains(&key) {
            self.pending_machine_relations
                .push((relation, first, second));
        }
    }

    /// Fires one queued relation. A firing interns nodes, whose registration
    /// queues further relations rather than firing them, so a long operator
    /// chain under a conversion is a loop, not a recursion; and the closing
    /// loop makes the firing's unions before the next relation, so a node
    /// the next one interns names its operands' classes, which have
    /// settled. Only the outermost closing loop fires.
    pub(super) fn fire_machine_relation(&mut self, pending: &mut PendingUnions) {
        if self.relating_machine_terms {
            return;
        }
        let Some((relation, first, second)) = self.pending_machine_relations.pop() else {
            return;
        };
        self.relating_machine_terms = true;
        match relation {
            Relation::Distribute => self.distribute(first, second, pending),
            Relation::Compose => self.compose(first, second, pending),
            Relation::Invert => self.invert(first, second, pending),
        }
        self.relating_machine_terms = false;
    }

    /// R-dist for the conversion `cast` over a class holding `operator`.
    fn distribute(&mut self, cast: u64, operator: u64, pending: &mut PendingUnions) {
        if self.fired_machine_relations.contains(&(cast, operator)) {
            return;
        }
        let (
            Some(Decoded::Cast { key, .. }),
            Some(Decoded::Operator {
                format,
                op,
                left,
                right,
            }),
        ) = (self.decode_machine(cast), self.decode_machine(operator))
        else {
            return;
        };
        if !key.truncates() || !key.source.reads_operator(format) {
            return;
        }
        let destination_bits = key.destination.format().bits();
        if op == SignFree::ShiftLeft {
            let count =
                right.and_then(|count| self.int32_constants.get(&self.root(count)).copied());
            if !count.is_some_and(|count| count >= 0 && (count as u32) < destination_bits) {
                return;
            }
        }
        self.fired_machine_relations = self.fired_machine_relations.with_value((cast, operator));
        crate::instrumentation::record_deterministic_work(1);
        let Some(left) = self.convert_like(cast, self.root(left), pending) else {
            return;
        };
        let right = match (op, right) {
            (SignFree::ShiftLeft, Some(count)) => Some(self.root(count)),
            (_, Some(right)) => match self.convert_like(cast, self.root(right), pending) {
                Some(right) => Some(right),
                None => return,
            },
            (_, None) => None,
        };
        if let Some(result) =
            self.intern_machine_operator(OperatorFormat::of(key.destination), op, left, right)
        {
            pending.push((cast, result));
        }
    }

    /// R-comp for the conversion `outer` over a class holding the
    /// conversion `inner`.
    fn compose(&mut self, outer: u64, inner: u64, pending: &mut PendingUnions) {
        if outer == inner || self.fired_machine_relations.contains(&(outer, inner)) {
            return;
        }
        let (
            Some(Decoded::Cast { key: outer_key, .. }),
            Some(Decoded::Cast {
                key: inner_key,
                operand,
            }),
        ) = (self.decode_machine(outer), self.decode_machine(inner))
        else {
            return;
        };
        let CastSource::Format(source) = inner_key.source else {
            return;
        };
        let destination = outer_key.destination;
        let bits = destination.format().bits();
        let exact =
            inner_key.preserves_value() && outer_key.source.reads_exactly(inner_key.destination);
        let low_bits = bits <= inner_key.destination.format().bits()
            // A full-width source has canonical bits. Reducing modulo the
            // intermediate width and then a no-wider destination is the
            // direct modular conversion, even when the intermediate changes
            // signedness. Narrow source words need the existing restriction.
            && (bits <= source.format().bits() || source.format().bits() >= 32)
            && outer_key.source.bits() == inner_key.destination.format().bits();
        if !exact && !low_bits {
            return;
        }
        self.fired_machine_relations = self.fired_machine_relations.with_value((outer, inner));
        crate::instrumentation::record_deterministic_work(1);
        let operand = self.root(operand);
        if let Some(result) = self.intern_conversion(source, destination, operand, pending) {
            pending.push((outer, result));
        }
    }

    /// R0 for a conversion between the two signednesses of one width: the
    /// conversion back of `cast` is in `operand`'s class.
    fn invert(&mut self, cast: u64, operand: u64, pending: &mut PendingUnions) {
        let Some(Decoded::Cast { key, .. }) = self.decode_machine(cast) else {
            return;
        };
        let CastSource::Format(source) = key.source else {
            return;
        };
        // The `int32` and `uint32` widenings of one narrow value are one
        // word (rule K1), so each is in the other's class.
        if crate::kernel::is_narrow_widening32(source, key.destination)
            && !self.fired_machine_relations.contains(&(cast, cast))
        {
            self.fired_machine_relations = self.fired_machine_relations.with_value((cast, cast));
            crate::instrumentation::record_deterministic_work(1);
            let other = if key.destination.format().is_signed() {
                MachineIntegerType::UInt32
            } else {
                MachineIntegerType::Int32
            };
            let sibling = self.intern_node(Node::Int32Unary(
                Int32Unary::Cast(source, other),
                self.root(operand),
            ));
            pending.push((cast, sibling));
            return;
        }
        // A narrow value is native, a value of its own width, so the two
        // signednesses of 8 or 16 bits are a bijection as at 32 and 64.
        if source.format().bits() != key.destination.format().bits()
            || source == key.destination
            || self.fired_machine_relations.contains(&(cast, cast))
        {
            return;
        }
        self.fired_machine_relations = self.fired_machine_relations.with_value((cast, cast));
        crate::instrumentation::record_deterministic_work(1);
        let class = self.root(cast);
        if let Some(back) = self.intern_conversion(key.destination, source, class, pending)
            && back != class
        {
            pending.push((back, operand));
        }
    }

    /// The conversion `cast` applies, applied to the class `value`.
    fn convert_like(&mut self, cast: u64, value: u64, pending: &mut PendingUnions) -> Option<u64> {
        match *self.applications.get(&cast)? {
            Application::Int32Unary(Int32Unary::Cast(source, destination), _) => {
                Some(self.narrow_cast_parts(source, destination, value, pending))
            }
            Application::Apply(function, _) => match self.machine_heads.get(&function).copied()? {
                MachineHead::Unary(U::MachineIntegerCast {
                    source,
                    destination,
                }) if representation::narrow_carrier_mask(destination).is_some() => {
                    Some(self.narrow_cast_parts(source, destination, value, pending))
                }
                MachineHead::Unary(_) => Some(self.intern_node(Node::Apply(function, value))),
                MachineHead::Binary(_) => None,
            },
            _ => None,
        }
    }

    /// The class of `Cast(source -> destination, value)`, interned as the
    /// term's conversion would be (`conversion::lower`). `None` where that
    /// node has no e-graph form here.
    fn intern_conversion(
        &mut self,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        value: u64,
        pending: &mut PendingUnions,
    ) -> Option<u64> {
        use crate::kernel::machine_integer::conversion::{self, ConversionLowering as L};
        let (from, to) = (source.format(), destination.format());
        let unary = |classes: &mut Self, op: U, width: crate::kernel::CarrierWidth| {
            let head = classes.intern_node(Node::MachineUnary(op, width));
            classes.intern_node(Node::Apply(head, value))
        };
        Some(
            match conversion::lower(source, destination, conversion::ConversionPolicy::Modular)
                .lowering
            {
                L::Identity => value,
                // σ names its operand's word (rule K1).
                L::SignCast => value,
                L::Cast if representation::narrow_carrier_mask(destination).is_some() => {
                    self.narrow_cast_parts(source, destination, value, pending)
                }
                // A 32-bit widening of a narrow value: a node of its own,
                // over an operand of the narrow width.
                L::Cast if from.bits() < 32 && to.bits() == 32 => self.intern_node(
                    Node::Int32Unary(Int32Unary::Cast(source, destination), value),
                ),
                L::Cast => unary(
                    self,
                    U::MachineIntegerCast {
                        source,
                        destination,
                    },
                    crate::kernel::CarrierWidth::of_machine_type(destination),
                ),
                L::LowWord => unary(self, U::UInt32From64, crate::kernel::CarrierWidth::Bits32),
                L::Extend64 => {
                    let op = match (to.is_signed(), from.is_signed()) {
                        (true, true) => U::Int64From32,
                        (true, false) => U::Int64FromUInt32,
                        (false, true) => U::UInt64FromInt32,
                        (false, false) => U::UInt64From32,
                    };
                    unary(self, op, crate::kernel::CarrierWidth::Bits64)
                }
                // `int64_from_uint64_bits` names the same 64-bit word.
                L::Reinterpret64 if to.is_signed() => value,
                L::Reinterpret64 => unary(
                    self,
                    U::UInt64FromInt64,
                    crate::kernel::CarrierWidth::Bits64,
                ),
            },
        )
    }

    /// The class of `left op right` at `format`, interned as the term's
    /// operator would be (`congruence`'s machine terms). `None` where the
    /// operator has no e-graph form at that format.
    fn intern_machine_operator(
        &mut self,
        format: OperatorFormat,
        op: SignFree,
        left: u64,
        right: Option<u64>,
    ) -> Option<u64> {
        use crate::kernel::CarrierWidth as W;
        let node = match (format, op, right) {
            (OperatorFormat::Word32, SignFree::Not, None) => {
                Node::Int32Unary(Int32Unary::Not, left)
            }
            (OperatorFormat::Word32, SignFree::Add, Some(right)) => Node::Int32Add(left, right),
            (OperatorFormat::Word32, SignFree::Xor, Some(right)) => {
                Node::Int32Binary(Int32Binary::BitwiseXor, left, right)
            }
            (OperatorFormat::Word32, op, Some(right)) => Node::Int32Binary(
                Int32Binary::Other(B::Machine(MachineIntegerType::Int32, op.binary()?)),
                left,
                right,
            ),
            (OperatorFormat::Format(format), SignFree::Not, None) => {
                let width = W::of_machine_type(format);
                let head = self.intern_node(Node::MachineUnary(
                    U::Machine(format, MachineUnaryOp::BitwiseNot),
                    width,
                ));
                Node::Apply(head, left)
            }
            (OperatorFormat::Format(MachineIntegerType::UInt64), op, Some(right))
                if op != SignFree::ShiftLeft =>
            {
                let op = match op {
                    SignFree::Add => UInt64Binary::Add,
                    SignFree::Subtract => UInt64Binary::Subtract,
                    SignFree::Multiply => UInt64Binary::Multiply,
                    SignFree::And => UInt64Binary::And,
                    SignFree::Or => UInt64Binary::Or,
                    SignFree::Xor => UInt64Binary::Xor,
                    SignFree::ShiftLeft | SignFree::Not => return None,
                };
                Node::UInt64Binary(op, left, right)
            }
            (OperatorFormat::Format(format), op, Some(right)) => {
                // A 64-bit shift's count is an opaque argument.
                if op == SignFree::ShiftLeft && format.format().bits() > 32 {
                    return None;
                }
                let head = self.intern_node(Node::MachineBinary(
                    B::Machine(format, op.binary()?),
                    W::of_machine_type(format),
                ));
                let partial = self.intern_node(Node::Apply(head, left));
                Node::Apply(partial, right)
            }
            _ => return None,
        };
        Some(self.intern_node(node))
    }
}
