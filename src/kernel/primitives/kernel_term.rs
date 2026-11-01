//! Shared typed expression nodes. Arithmetic and calls migrate first; the
//! explicitly named Legacy leaf is a lossless boundary for unmigrated sorts.
//! No constructor consults facts, evaluates arithmetic, or unfolds a call.
use super::*;
mod boolean;
mod machine;
pub use machine::{KernelMachineCastEncoding, KernelMachineLiteral};
use num_bigint::BigInt;
use std::collections::{HashMap, VecDeque};
use std::sync::{Mutex, Weak};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum KernelType {
    Bool,
    Integer,
    C(CType),
    Algebraic(AlgebraicType),
    ArrayRef(CType),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum KernelIntegerOperator {
    Negate,
    Add,
    Subtract,
    Multiply,
    TruncatingQuotient,
    TruncatingRemainder,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum KernelTermNode {
    BoolLiteral(bool),
    BoolCast {
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    BoolCompare {
        format: MachineIntegerType,
        relation: CompareRelation,
        arguments: [KernelTerm; 2],
    },
    IntegerCompare {
        operator: IntegerComparisonOperator,
        arguments: [KernelTerm; 2],
    },
    BoolEqual {
        arguments: [KernelTerm; 2],
    },
    BoolIf {
        arguments: [KernelTerm; 3],
    },
    /// Exact condition payload at the temporary migration boundary.
    LegacyBool(KernelLegacyTerm),
    IntegerLiteral(BigInt),
    MachineLiteral(KernelMachineLiteral),
    IntegerToMachine {
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    MachineObservation {
        format: MachineIntegerType,
        operand: KernelTerm,
    },
    MachineBinary {
        format: MachineIntegerType,
        operator: MachineBinaryOp,
        arguments: [KernelTerm; 2],
    },
    MachineUnary {
        format: MachineIntegerType,
        operator: MachineUnaryOp,
        operand: KernelTerm,
    },
    MachineCast {
        encoding: KernelMachineCastEncoding,
        source: MachineIntegerType,
        destination: MachineIntegerType,
        operand: KernelTerm,
    },
    Variable(Variable),
    IntegerOperation {
        operator: KernelIntegerOperator,
        arguments: Vec<KernelTerm>,
    },
    Call {
        name: String,
        arguments: Vec<KernelTerm>,
    },
    /// Temporary adapter, not a second spelling or equality interpretation.
    Legacy(KernelLegacyTerm),
}

/// An exact unmigrated payload, with identity supplied by its producer.
/// C pointer equality intentionally omits auxiliary qualifiers/evidence, so
/// it cannot be used to select which legacy payload a bridge returns.
#[derive(Clone, Debug)]
pub struct KernelLegacyTerm {
    identity: LegacyIdentity,
    value: PureFunctionArgument,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum LegacyIdentity {
    Integer(u64),
    ApplicationArgument(SharedPureApplication, usize),
    Fresh(u64),
}
impl PartialEq for KernelLegacyTerm {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for KernelLegacyTerm {}
impl Hash for KernelLegacyTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}
impl KernelLegacyTerm {
    pub fn value(&self) -> &PureFunctionArgument {
        &self.value
    }
}

struct TermData {
    id: u64,
    key: NodeKey,
    // Temporary reverse bridge. Weak because the old node caches this term.
    integer: Mutex<WeakIntegerTerm>,
}

struct NodeKeyData {
    fingerprint: u64,
    ty: KernelType,
    node: KernelTermNode,
}
#[derive(Clone)]
struct NodeKey(Arc<NodeKeyData>);
impl PartialEq for NodeKey {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || (self.0.ty == other.0.ty && self.0.node == other.0.node)
    }
}
impl Eq for NodeKey {}
impl Hash for NodeKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl NodeKey {
    fn new(ty: KernelType, node: KernelTermNode) -> Self {
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        ty.hash(&mut hash);
        node.hash(&mut hash);
        Self(Arc::new(NodeKeyData {
            fingerprint: hash.finish(),
            ty,
            node,
        }))
    }
}

/// Immutable typed term. Identity is structural, never an equality-class id.
/// Migrated children are handles, so hashing and comparing an arithmetic or
/// call node do not walk its DAG. Legacy payload costs remain explicit input.
#[derive(Clone)]
pub struct KernelTerm(Arc<TermData>);

impl std::fmt::Debug for KernelTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KernelTerm")
            .field("id", &self.0.id)
            .field("type", &self.0.key.0.ty)
            .finish()
    }
}
impl PartialEq for KernelTerm {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for KernelTerm {}
impl Hash for KernelTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}

#[derive(Default)]
struct Interner {
    terms: HashMap<NodeKey, Weak<TermData>>,
    cleanup: VecDeque<NodeKey>,
    next_id: u64,
}
impl Interner {
    fn intern(&mut self, key: NodeKey) -> KernelTerm {
        // Bounded upkeep. A dead parent's key may retain child handles until
        // this queue reaches it, but no whole interner scan is performed.
        for _ in 0..self.cleanup.len().min(8) {
            let key = self.cleanup.pop_front().unwrap();
            if self
                .terms
                .get(&key)
                .is_some_and(|value| value.strong_count() == 0)
            {
                self.terms.remove(&key);
            } else {
                self.cleanup.push_back(key);
            }
        }
        if let Some(existing) = self.terms.get(&key).and_then(Weak::upgrade) {
            return KernelTerm(existing);
        }
        let id = self.next_id;
        self.next_id = id.checked_add(1).expect("kernel term identity exhausted");
        let value = Arc::new(TermData {
            id,
            key: key.clone(),
            integer: Mutex::default(),
        });
        self.terms.insert(key.clone(), Arc::downgrade(&value));
        self.cleanup.push_back(key);
        KernelTerm(value)
    }
}
impl KernelTerm {
    fn legacy_integer(&self) -> Option<SharedIntegerTerm> {
        self.0
            .integer
            .lock()
            .expect("term bridge poisoned")
            .upgrade()
    }
    fn remember_integer(&self, integer: &SharedIntegerTerm) {
        *self.0.integer.lock().expect("term bridge poisoned") = integer.downgrade();
        // A legacy leaf owns its old value. Caching it on that same value
        // would create a cycle; only genuinely migrated nodes cache both ways.
        if !matches!(self.node(), KernelTermNode::Legacy(_)) {
            integer.remember_kernel_term(self.clone());
        }
    }

    fn intern(ty: KernelType, node: KernelTermNode) -> Self {
        static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
        crate::instrumentation::record_deterministic_work(match &node {
            KernelTermNode::IntegerOperation { arguments, .. } => arguments.len() + 1,
            KernelTermNode::Call { name, arguments } => name.len() + arguments.len() + 1,
            KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
            _ => 1,
        });
        let key = NodeKey::new(ty, node);
        INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("kernel term interner poisoned")
            .intern(key)
    }
    pub fn ty(&self) -> &KernelType {
        &self.0.key.0.ty
    }
    pub fn node(&self) -> &KernelTermNode {
        &self.0.key.0.node
    }
    /// Immediate expression operands; unmigrated leaves remain opaque.
    pub fn children(&self) -> &[Self] {
        match self.node() {
            KernelTermNode::IntegerOperation { arguments, .. }
            | KernelTermNode::Call { arguments, .. } => arguments,
            KernelTermNode::MachineBinary { arguments, .. }
            | KernelTermNode::BoolCompare { arguments, .. }
            | KernelTermNode::IntegerCompare { arguments, .. }
            | KernelTermNode::BoolEqual { arguments } => arguments,
            KernelTermNode::BoolIf { arguments } => arguments,
            KernelTermNode::BoolCast { operand, .. }
            | KernelTermNode::IntegerToMachine { operand, .. }
            | KernelTermNode::MachineObservation { operand, .. }
            | KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => std::slice::from_ref(operand),
            _ => &[],
        }
    }

    pub(crate) fn bool_cast(
        destination: MachineIntegerType,
        operand: KernelTerm,
    ) -> Result<Self, &'static str> {
        if operand.ty() != &KernelType::Bool {
            return Err("Boolean conversion requires a Bool operand");
        }
        Ok(Self::intern(
            KernelType::C(destination.c_type()),
            KernelTermNode::BoolCast {
                destination,
                operand,
            },
        ))
    }

    pub(crate) fn integer_to_machine(
        destination: MachineIntegerType,
        operand: KernelTerm,
    ) -> Result<Self, &'static str> {
        if operand.ty() != &KernelType::Integer {
            return Err("machine conversion requires an Integer operand");
        }
        Ok(Self::intern(
            KernelType::C(destination.c_type()),
            KernelTermNode::IntegerToMachine {
                destination,
                operand,
            },
        ))
    }

    pub fn integer_literal(value: BigInt) -> Self {
        Self::intern(KernelType::Integer, KernelTermNode::IntegerLiteral(value))
    }
    pub fn variable(ty: KernelType, variable: Variable) -> Self {
        Self::intern(ty, KernelTermNode::Variable(variable))
    }
    pub fn integer_operation(
        operator: KernelIntegerOperator,
        arguments: Vec<Self>,
    ) -> Result<Self, &'static str> {
        let arity = if operator == KernelIntegerOperator::Negate {
            1
        } else {
            2
        };
        if arguments.len() != arity || arguments.iter().any(|arg| arg.ty() != &KernelType::Integer)
        {
            return Err("Integer operation requires Integer operands of the declared arity");
        }
        Ok(Self::intern(
            KernelType::Integer,
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            },
        ))
    }
    /// Called after the existing declaration checker resolves the signature.
    pub(crate) fn checked_call(ty: KernelType, name: String, arguments: Vec<Self>) -> Self {
        Self::intern(ty, KernelTermNode::Call { name, arguments })
    }
    fn legacy(argument: PureFunctionArgument) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let identity = match &argument {
            PureFunctionArgument::Integer(value) => LegacyIdentity::Integer(value.id()),
            _ => LegacyIdentity::Fresh(
                NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
                    .expect("legacy term identity exhausted"),
            ),
        };
        Self::legacy_at(argument, identity)
    }
    fn legacy_at(argument: PureFunctionArgument, identity: LegacyIdentity) -> Self {
        let ty = match &argument {
            PureFunctionArgument::Integer(_) => KernelType::Integer,
            PureFunctionArgument::Value(value) => KernelType::C(value.c_type()),
            PureFunctionArgument::Algebraic(value) => {
                KernelType::Algebraic(value.algebraic_type.clone())
            }
            PureFunctionArgument::ArrayRef { element_type, .. } => {
                KernelType::ArrayRef(*element_type)
            }
        };
        Self::intern(
            ty,
            KernelTermNode::Legacy(KernelLegacyTerm {
                identity,
                value: argument,
            }),
        )
    }
}

/// One conversion per shared source node, including shared call arguments.
/// This bridge is removed as producers construct KernelTerm directly.
#[derive(Default)]
pub(crate) struct KernelTermImport {
    integers: HashMap<SharedIntegerTerm, KernelTerm>,
}
impl KernelTermImport {
    pub(crate) fn argument(&mut self, value: &PureFunctionArgument) -> KernelTerm {
        match value {
            PureFunctionArgument::Integer(value) => self.integer(value),
            PureFunctionArgument::Value(value) if matches!(value, integer_c_value!(_)) => {
                let format = MachineIntegerType::from_c_type(value.c_type()).unwrap();
                let (integer_c_value!(bits)) = value else {
                    unreachable!()
                };
                self.machine(format, bits)
            }
            _ => KernelTerm::legacy(value.clone()),
        }
    }
    pub(crate) fn integer(&mut self, term: &SharedIntegerTerm) -> KernelTerm {
        if let Some(value) = term.kernel_term() {
            return value.clone();
        }
        if let Some(value) = self.integers.get(term) {
            return value.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        use KernelIntegerOperator as Op;
        let value = match term.as_ref() {
            IntegerTerm::Constant(value) => KernelTerm::integer_literal(value.clone()),
            IntegerTerm::Variable(variable) => KernelTerm::variable(KernelType::Integer, *variable),
            IntegerTerm::Machine(machine) => KernelTerm::intern(
                KernelType::Integer,
                KernelTermNode::MachineObservation {
                    format: machine.ty(),
                    operand: self.machine(machine.ty(), machine.value()),
                },
            ),
            IntegerTerm::Negate(inner) => {
                KernelTerm::integer_operation(Op::Negate, vec![self.integer(inner)]).unwrap()
            }
            IntegerTerm::Add(a, b)
            | IntegerTerm::Subtract(a, b)
            | IntegerTerm::Multiply(a, b)
            | IntegerTerm::TruncatingQuotient(a, b)
            | IntegerTerm::TruncatingRemainder(a, b) => {
                let operator = match term.as_ref() {
                    IntegerTerm::Add(..) => Op::Add,
                    IntegerTerm::Subtract(..) => Op::Subtract,
                    IntegerTerm::Multiply(..) => Op::Multiply,
                    IntegerTerm::TruncatingQuotient(..) => Op::TruncatingQuotient,
                    _ => Op::TruncatingRemainder,
                };
                KernelTerm::integer_operation(operator, vec![self.integer(a), self.integer(b)])
                    .unwrap()
            }
            IntegerTerm::PureFunctionApplication(application) => {
                let arguments = application
                    .arguments()
                    .iter()
                    .enumerate()
                    .map(|(index, arg)| match arg {
                        PureFunctionArgument::Integer(value) => self.integer(value),
                        PureFunctionArgument::Value(value)
                            if matches!(value, integer_c_value!(_)) =>
                        {
                            self.argument(arg)
                        }
                        _ => KernelTerm::legacy_at(
                            arg.clone(),
                            LegacyIdentity::ApplicationArgument(application.clone(), index),
                        ),
                    })
                    .collect();
                KernelTerm::checked_call(KernelType::Integer, application.name().into(), arguments)
            }
            // Binders and their scoped obligations keep
            // their exact old representation until their own migration.
            _ => KernelTerm::legacy(PureFunctionArgument::Integer(term.clone())),
        };
        value.remember_integer(term);
        self.integers.insert(term.clone(), value.clone());
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reverse_bridge_does_not_keep_the_source_node_alive() {
        let source: SharedIntegerTerm = IntegerTerm::Variable(Variable(87654321)).into();
        let weak = source.downgrade();
        let common = KernelTermImport::default().integer(&source);
        drop(source);
        assert!(weak.upgrade().is_none());
        assert_eq!(common.ty(), &KernelType::Integer);
        let reconstructed = KernelTermExport::default().integer(&common).unwrap();
        assert_eq!(reconstructed.kernel_term(), Some(&common));
    }

    #[test]
    fn machine_observation_retains_its_format_and_reconstructs_after_source_drop() {
        let word = Bitvector32Term::Variable(Variable(87654322));
        let mut observations = Vec::new();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let machine = SharedMachineIntegerTerm::intern(format, word.clone());
            let source: SharedIntegerTerm = IntegerTerm::Machine(machine.clone()).into();
            let common = KernelTermImport::default().integer(&source);
            assert!(
                matches!(common.node(), KernelTermNode::MachineObservation { format: actual, .. } if *actual == format)
            );
            assert_eq!(common.ty(), &KernelType::Integer);
            assert_eq!(common.children()[0].ty(), &KernelType::C(format.c_type()));
            drop(source);
            let restored = KernelTermExport::default().integer(&common).unwrap();
            assert!(
                matches!(restored.as_ref(), IntegerTerm::Machine(actual) if actual.id() == machine.id())
            );
            observations.push(common);
        }
        assert_ne!(observations[0], observations[1]);
        assert_ne!(observations[2], observations[3]);
    }

    #[test]
    fn checker_bridge_preserves_calls_and_machine_types() {
        let input =
            PureFunctionArgument::Value(CValue::UInt32(Bitvector32Term::Variable(Variable(70))));
        let call = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "foo".into(),
            vec![input],
        ));
        let source: SharedIntegerTerm =
            IntegerTerm::Add(IntegerTerm::Variable(Variable(71)).into(), call.into()).into();
        let common = KernelTermImport::default().integer(&source);
        assert_eq!(common.children().len(), 2);
        assert!(matches!(
            common.children()[1].node(),
            KernelTermNode::Call { .. }
        ));
        assert_eq!(
            common.children()[1].children()[0].ty(),
            &KernelType::C(CType::UInt32)
        );
        assert_eq!(
            KernelTermExport::default().integer(&common).unwrap(),
            source
        );
    }

    #[test]
    fn legacy_pointer_equality_does_not_discard_auxiliary_qualifiers() {
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(76)), CType::Int32Pointer);
        let constant = pointer.clone().with_pointee_constant(true);
        assert_eq!(
            pointer, constant,
            "const is auxiliary, not pointer identity"
        );
        let mut import = KernelTermImport::default();
        let plain = import.argument(&PureFunctionArgument::Value(CValue::Pointer(pointer)));
        let qualified = import.argument(&PureFunctionArgument::Value(CValue::Pointer(constant)));
        let PureFunctionArgument::Value(CValue::Pointer(restored)) =
            KernelTermExport::default().argument(&qualified).unwrap()
        else {
            panic!("pointer")
        };
        assert!(restored.pointee_constant());
        let PureFunctionArgument::Value(CValue::Pointer(restored)) =
            KernelTermExport::default().argument(&plain).unwrap()
        else {
            panic!("pointer")
        };
        assert!(!restored.pointee_constant());
    }

    #[test]
    fn legacy_adapter_keeps_complete_pointers_and_scoped_integer_nodes() {
        let base = Pointer::symbolic(Variable(75));
        let root = CPointerValue::new(base.clone(), CType::Int32Pointer);
        let member = root.clone().with_extent(Some(SubobjectExtent {
            start: base,
            width: 4u32.into(),
        }));
        let mut import = KernelTermImport::default();
        let root = PureFunctionArgument::Value(CValue::Pointer(root));
        let member = PureFunctionArgument::Value(CValue::Pointer(member));
        let root_term = import.argument(&root);
        let member_term = import.argument(&member);
        assert_ne!(root_term, member_term);
        let mut export = KernelTermExport::default();
        assert_eq!(export.argument(&root_term).unwrap(), root);
        assert_eq!(export.argument(&member_term).unwrap(), member);
        let conditional: SharedIntegerTerm = IntegerTerm::If {
            condition: Box::new(ConditionTerm::Constant(true)),
            then_term: IntegerTerm::constant_i64(1).into(),
            else_term: IntegerTerm::constant_i64(2).into(),
        }
        .into();
        assert_eq!(
            export.integer(&import.integer(&conditional)).unwrap(),
            conditional
        );
    }

    #[test]
    fn structural_identity_preserves_operations_types_and_call_arguments() {
        let a = KernelTerm::variable(KernelType::Integer, Variable(71));
        let b = KernelTerm::variable(KernelType::Integer, Variable(72));
        let call = KernelTerm::checked_call(KernelType::Integer, "foo".into(), vec![b.clone()]);
        let sum = KernelTerm::integer_operation(
            KernelIntegerOperator::Add,
            vec![a.clone(), call.clone()],
        )
        .unwrap();
        assert_eq!(
            sum,
            KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![a, call]).unwrap()
        );
        assert_ne!(
            b,
            KernelTerm::variable(KernelType::C(CType::Int32), Variable(72))
        );
        let one = KernelTerm::integer_literal(1.into());
        assert_ne!(
            KernelTerm::integer_operation(KernelIntegerOperator::Add, vec![one.clone(), one])
                .unwrap(),
            KernelTerm::integer_literal(2.into())
        );
        assert!(
            KernelTerm::integer_operation(
                KernelIntegerOperator::Negate,
                vec![KernelTerm::variable(
                    KernelType::C(CType::Int32),
                    Variable(72)
                )]
            )
            .is_err()
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/primitives/kernel_term.rs");
}

/// Lossless bridge back to the existing checker. No normalizing constructors.
#[derive(Default)]
pub(crate) struct KernelTermExport {
    values: HashMap<KernelTerm, PureFunctionArgument>,
}
impl KernelTermExport {
    pub(crate) fn argument(
        &mut self,
        term: &KernelTerm,
    ) -> Result<PureFunctionArgument, &'static str> {
        if let Some(value) = term.legacy_integer() {
            return Ok(PureFunctionArgument::Integer(value));
        }
        if let KernelType::C(c_type) = term.ty()
            && let Some(format) = MachineIntegerType::from_c_type(*c_type)
            && !matches!(term.node(), KernelTermNode::Legacy(_))
        {
            // Export the explicit boxed output once. Caching and then cloning
            // every intermediate boxed subtree would make a chain quadratic.
            return Ok(PureFunctionArgument::Value(machine::wrap_exact(
                format,
                Self::machine(term)?,
            )));
        }
        if let Some(value) = self.values.get(term) {
            return Ok(value.clone());
        }
        crate::instrumentation::record_deterministic_work(match term.node() {
            KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
            KernelTermNode::IntegerOperation { arguments, .. } => arguments.len() + 1,
            KernelTermNode::Call { name, arguments } => name.len() + arguments.len() + 1,
            _ => 1,
        });
        let value = match term.node() {
            KernelTermNode::Legacy(value) => value.value().clone(),
            KernelTermNode::IntegerLiteral(value) => {
                PureFunctionArgument::Integer(IntegerTerm::Constant(value.clone()).into())
            }
            KernelTermNode::Variable(variable) if term.ty() == &KernelType::Integer => {
                PureFunctionArgument::Integer(IntegerTerm::Variable(*variable).into())
            }
            KernelTermNode::MachineObservation { format, operand } => {
                PureFunctionArgument::Integer(
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        *format,
                        Self::machine(operand)?,
                    ))
                    .into(),
                )
            }
            KernelTermNode::IntegerOperation {
                operator,
                arguments,
            } => {
                let mut args = arguments
                    .iter()
                    .map(|arg| self.integer(arg))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter();
                let a = args.next().unwrap();
                use KernelIntegerOperator as Op;
                let value = match operator {
                    Op::Negate => IntegerTerm::Negate(a),
                    Op::Add => IntegerTerm::Add(a, args.next().unwrap()),
                    Op::Subtract => IntegerTerm::Subtract(a, args.next().unwrap()),
                    Op::Multiply => IntegerTerm::Multiply(a, args.next().unwrap()),
                    Op::TruncatingQuotient => {
                        IntegerTerm::TruncatingQuotient(a, args.next().unwrap())
                    }
                    Op::TruncatingRemainder => {
                        IntegerTerm::TruncatingRemainder(a, args.next().unwrap())
                    }
                };
                PureFunctionArgument::Integer(value.into())
            }
            KernelTermNode::Call { name, arguments } if term.ty() == &KernelType::Integer => {
                let arguments = arguments
                    .iter()
                    .map(|arg| self.argument(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                PureFunctionArgument::Integer(
                    IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                        name.clone(),
                        arguments,
                    ))
                    .into(),
                )
            }
            _ => return Err("kernel term sort has not migrated to the checker bridge"),
        };
        if let PureFunctionArgument::Integer(integer) = &value {
            term.remember_integer(integer);
        }
        self.values.insert(term.clone(), value.clone());
        Ok(value)
    }
    pub(crate) fn integer(&mut self, term: &KernelTerm) -> Result<SharedIntegerTerm, &'static str> {
        match self.argument(term)? {
            PureFunctionArgument::Integer(value) => Ok(value),
            _ => Err("expected Integer kernel term"),
        }
    }
}
