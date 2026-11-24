//! Scalar storage identity follows the native variant and field order.
//! Shared arithmetic projects each selected DAG node once.
use super::*;
use crate::kernel::{MachineCastSpelling, MachineUnaryOp};

#[derive(Clone, Debug)]
pub(in crate::kernel) struct ScalarStorageKey(Arc<ScalarKeyData>);
#[derive(Debug)]
struct ScalarKeyData {
    shape: ScalarShape,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum ScalarShape {
    Atom(MachineTerm),
    WordBinary(MachineBinaryOp, MachineIntegerType, [ScalarStorageKey; 2]),
    WordUnary(MachineIntegerType, MachineUnaryOp, ScalarStorageKey),
    If(ConditionStorageKey, [ScalarStorageKey; 2]),
    Fold([ScalarStorageKey; 4], Variable, Variable),
    Match(AlgebraicStorageKey, Vec<MatchArmKey>),
    Address(AddressKey),
    IntegerConversion(SharedIntegerTerm, MachineIntegerType),
    Cast(
        MachineCastSpelling,
        ScalarStorageKey,
        MachineIntegerType,
        MachineIntegerType,
    ),
    BoolCast(MachineIntegerType, ConditionStorageKey),
    Negate(bool, ScalarStorageKey),
    Binary(bool, FloatBinaryOperator, [ScalarStorageKey; 2]),
    Application(String, Vec<ScalarStorageKey>),
    Call(String, Vec<ArgumentKey>),
}
#[derive(Debug, Hash)]
struct MatchArmKey {
    variant: String,
    bindings: Vec<AlgebraicStorageKey>,
    body: ScalarStorageKey,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum ArgumentKey {
    Program(ProgramStorageKey),
    SharedMachine(SharedMachineIntegerTerm),
    Integer(SharedIntegerTerm),
    Algebraic(AlgebraicStorageKey),
    Array(ProgramPoint, ProgramStorageKey, ProgramType),
}
impl ArgumentKey {
    pub(super) fn native(value: &PureFunctionArgument) -> Self {
        match value {
            PureFunctionArgument::Value(value) => Self::Program(ProgramStorageKey::native(value)),
            PureFunctionArgument::SharedMachine(value) => Self::SharedMachine(value.clone()),
            PureFunctionArgument::Integer(value) => Self::Integer(value.clone()),
            PureFunctionArgument::Algebraic(value) => {
                Self::Algebraic(AlgebraicStorageKey::native(value))
            }
            PureFunctionArgument::ArrayRef {
                point,
                pointer,
                element_type,
            } => Self::Array(
                point.clone(),
                ProgramStorageKey::native(pointer),
                *element_type,
            ),
        }
    }

    pub(super) fn shared(root: &KernelTerm) -> Self {
        if let Some(value) = root.written_argument() {
            return Self::native(value);
        }
        match root.node() {
            KernelTermNode::ObservedPointer(value) => Self::shared(value.source()),
            KernelTermNode::ArrayReference {
                point,
                pointer,
                element_type,
            } => Self::Array(
                point.clone(),
                ProgramStorageKey::shared(pointer),
                *element_type,
            ),
            _ => match root.ty() {
                KernelType::Integer => Self::Integer(SharedIntegerTerm::from_root(root.clone())),
                KernelType::Algebraic(_) => Self::Algebraic(algebraic_for_root(root)),
                _ => Self::Program(ProgramStorageKey::shared(root)),
            },
        }
    }
}
impl ScalarStorageKey {
    fn new(shape: ScalarShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(ScalarKeyData {
            shape,
            fingerprint: hash.finish(),
        }))
    }
    pub(in crate::kernel) fn native(value: &MachineTerm) -> Self {
        #[derive(Clone, Copy)]
        enum Task<'a> {
            Term(&'a MachineTerm),
            Argument(&'a PureFunctionArgument),
            Negate(bool),
            Binary(bool, FloatBinaryOperator),
            Application(&'a str, usize),
            Call(&'a str, usize),
            ScalarArgument(ProgramType),
            WordBinary(MachineBinaryOp, MachineIntegerType),
            WordUnary(MachineIntegerType, MachineUnaryOp),
            If(&'a ConditionTerm),
            Fold(Variable, Variable),
            Match(&'a AlgebraicTerm, &'a [AlgebraicBitvectorMatchArm]),
            Cast(MachineCastSpelling, MachineIntegerType, MachineIntegerType),
        }
        let mut pending = vec![Task::Term(value)];
        let mut values = Vec::new();
        let mut arguments = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Term(MachineTerm::Binary {
                    op,
                    format,
                    left,
                    right,
                }) => {
                    pending.extend([
                        Task::WordBinary(*op, *format),
                        Task::Term(right),
                        Task::Term(left),
                    ]);
                }
                Task::Term(MachineTerm::Unary {
                    format,
                    op,
                    operand,
                }) => {
                    pending.extend([Task::WordUnary(*format, *op), Task::Term(operand)]);
                }
                Task::Term(MachineTerm::If {
                    condition,
                    then_term,
                    else_term,
                }) => {
                    pending.extend([
                        Task::If(condition),
                        Task::Term(else_term),
                        Task::Term(then_term),
                    ]);
                }
                Task::Term(MachineTerm::RangeFold {
                    start,
                    end,
                    initial,
                    accumulator,
                    item,
                    body,
                }) => {
                    pending.push(Task::Fold(*accumulator, *item));
                    pending.extend([body, initial, end, start].map(|term| Task::Term(term)));
                }
                Task::Term(MachineTerm::AlgebraicMatch { scrutinee, arms }) => {
                    pending.push(Task::Match(scrutinee, arms));
                    pending.extend(arms.iter().rev().map(|arm| Task::Term(&arm.body)));
                }
                Task::Term(MachineTerm::IntegerAddress(address, _)) => {
                    values.push(Self::new(ScalarShape::Address(AddressKey::native(address))));
                }
                Task::Term(MachineTerm::IntegerToMachine { value, destination }) => {
                    values.push(Self::new(ScalarShape::IntegerConversion(
                        value.clone(),
                        *destination,
                    )));
                }
                Task::Term(MachineTerm::Cast {
                    spelling,
                    value,
                    from,
                    to,
                }) => {
                    pending.extend([Task::Cast(*spelling, *from, *to), Task::Term(value)]);
                }
                Task::Term(MachineTerm::BoolCast { to, value }) => {
                    values.push(Self::new(ScalarShape::BoolCast(
                        *to,
                        ConditionStorageKey::native(value),
                    )));
                }
                Task::Term(MachineTerm::Float32Negate(v)) => {
                    pending.push(Task::Negate(false));
                    pending.push(Task::Term(v));
                }
                Task::Term(MachineTerm::Float64Negate(v)) => {
                    pending.push(Task::Negate(true));
                    pending.push(Task::Term(v));
                }
                Task::Term(MachineTerm::Float32Binary {
                    operator,
                    left,
                    right,
                })
                | Task::Term(MachineTerm::Float64Binary {
                    operator,
                    left,
                    right,
                }) => {
                    let Task::Term(term) = task else {
                        unreachable!()
                    };
                    pending.push(Task::Binary(
                        matches!(term, MachineTerm::Float64Binary { .. }),
                        *operator,
                    ));
                    pending.push(Task::Term(right));
                    pending.push(Task::Term(left));
                }
                Task::Term(MachineTerm::PureFunctionApplication { name, arguments }) => {
                    pending.push(Task::Application(name, arguments.len()));
                    pending.extend(arguments.iter().rev().map(Task::Term));
                }
                Task::Term(MachineTerm::ClickFunctionApplication { name, arguments }) => {
                    pending.push(Task::Call(name, arguments.len()));
                    pending.extend(arguments.iter().rev().map(Task::Argument));
                }
                Task::Term(term) => values.push(Self::new(ScalarShape::Atom(term.clone()))),
                Task::Argument(PureFunctionArgument::Value(
                    value @ (crate::kernel::integer_c_value!(word)
                    | ProgramValue::Float32(word)
                    | ProgramValue::Float64(word)),
                )) => {
                    pending.extend([Task::ScalarArgument(value.program_type()), Task::Term(word)]);
                }
                Task::Argument(value) => arguments.push(ArgumentKey::native(value)),
                Task::ScalarArgument(ty) => {
                    let value = values.pop().unwrap();
                    arguments.push(ArgumentKey::Program(ProgramStorageKey::Scalar(ty, value)));
                }
                Task::WordBinary(op, format) => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::WordBinary(op, format, [a, b])));
                }
                Task::WordUnary(format, op) => {
                    let child = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::WordUnary(format, op, child)));
                }
                Task::If(guard) => {
                    let no = values.pop().unwrap();
                    let yes = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::If(
                        ConditionStorageKey::native(guard),
                        [yes, no],
                    )));
                }
                Task::Fold(accumulator, item) => {
                    let children = values
                        .split_off(values.len() - 4)
                        .try_into()
                        .expect("fold children");
                    values.push(Self::new(ScalarShape::Fold(children, accumulator, item)));
                }
                Task::Match(scrutinee, arms) => {
                    let bodies = values.split_off(values.len() - arms.len());
                    let arms = arms
                        .iter()
                        .zip(bodies)
                        .map(|(arm, body)| MatchArmKey {
                            variant: arm.variant.clone(),
                            bindings: arm
                                .bindings
                                .iter()
                                .map(AlgebraicStorageKey::native_field)
                                .collect(),
                            body,
                        })
                        .collect();
                    values.push(Self::new(ScalarShape::Match(
                        AlgebraicStorageKey::native(scrutinee),
                        arms,
                    )));
                }
                Task::Cast(spelling, source, destination) => {
                    let child = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::Cast(
                        spelling,
                        child,
                        source,
                        destination,
                    )));
                }
                Task::Negate(wide) => {
                    let value = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::Negate(wide, value)));
                }
                Task::Binary(wide, operator) => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::new(ScalarShape::Binary(wide, operator, [a, b])));
                }
                Task::Application(name, n) => {
                    let children = values.split_off(values.len() - n);
                    values.push(Self::new(ScalarShape::Application(name.into(), children)));
                }
                Task::Call(name, n) => {
                    let children = arguments.split_off(arguments.len() - n);
                    values.push(Self::new(ScalarShape::Call(name.into(), children)));
                }
            }
        }
        values.pop().expect("scalar key")
    }
    pub(in crate::kernel) fn shared(root: &KernelTerm) -> Self {
        let float = FloatOperandView::from_shared(root);
        let wide = root.ty() == &KernelType::Program(ProgramType::Float64);
        Self::new(match root.node() {
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            } => ScalarShape::WordBinary(
                *operator,
                *format,
                arguments.each_ref().map(KernelTerm::scalar_storage_key),
            ),
            KernelTermNode::MachineUnary {
                format,
                operator,
                operand,
            } => ScalarShape::WordUnary(*format, *operator, operand.scalar_storage_key()),
            KernelTermNode::MachineIf {
                arguments: [guard, yes, no],
            } => ScalarShape::If(
                guard.condition_storage_key(),
                [yes.scalar_storage_key(), no.scalar_storage_key()],
            ),
            KernelTermNode::Fold(fold) => ScalarShape::Fold(
                fold.arguments
                    .each_ref()
                    .map(KernelTerm::scalar_storage_key),
                fold.accumulator,
                fold.item,
            ),
            KernelTermNode::Match(matched) => ScalarShape::Match(
                algebraic_for_root(&matched.arguments[0]),
                matched
                    .arms
                    .iter()
                    .zip(&matched.arguments[1..])
                    .map(|(arm, body)| MatchArmKey {
                        variant: arm.variant.clone(),
                        bindings: arm
                            .bindings
                            .iter()
                            .map(AlgebraicStorageKey::field)
                            .collect(),
                        body: body.scalar_storage_key(),
                    })
                    .collect(),
            ),
            KernelTermNode::IntegerAddress { address, .. } => {
                ScalarShape::Address(AddressKey::shared(address))
            }
            KernelTermNode::IntegerToMachine {
                destination,
                operand,
            } => ScalarShape::IntegerConversion(
                SharedIntegerTerm::from_root(operand.clone()),
                *destination,
            ),
            KernelTermNode::MachineCast {
                encoding,
                source,
                destination,
                operand,
            } => {
                let (source, destination) =
                    encoding.legacy_formats().unwrap_or((*source, *destination));
                ScalarShape::Cast(*encoding, operand.scalar_storage_key(), source, destination)
            }
            KernelTermNode::BoolCast {
                destination,
                operand,
            } => ScalarShape::BoolCast(*destination, operand.condition_storage_key()),
            KernelTermNode::FloatNegate { operand } => {
                ScalarShape::Negate(wide, operand.scalar_storage_key())
            }
            KernelTermNode::FloatBinary {
                operator,
                arguments,
            } => ScalarShape::Binary(
                wide,
                *operator,
                arguments.each_ref().map(KernelTerm::scalar_storage_key),
            ),
            KernelTermNode::FloatConvert {
                source,
                destination,
                operand,
            } => {
                let destination = float.map_or(*destination, |view| view.format().program_type());
                let name = format!(
                    "c_{}_to_{}",
                    crate::kernel::program_type_spelling(*source),
                    crate::kernel::program_type_spelling(destination)
                );
                ScalarShape::Application(name, vec![operand.scalar_storage_key()])
            }
            KernelTermNode::FloatCall(call) => ScalarShape::Call(
                call.name.clone(),
                call.arguments
                    .iter()
                    .zip(&call.shared_machine_arguments)
                    .map(|(root, carrier)| match carrier {
                        Some(carrier) => ArgumentKey::SharedMachine(carrier.clone()),
                        None => ArgumentKey::shared(root),
                    })
                    .collect(),
            ),
            KernelTermNode::Call { name, arguments } => ScalarShape::Call(
                name.clone(),
                arguments.iter().map(ArgumentKey::shared).collect(),
            ),
            KernelTermNode::Variable(variable) => {
                ScalarShape::Atom(MachineTerm::Variable(*variable))
            }
            KernelTermNode::MachineLiteral(literal) => ScalarShape::Atom(literal.legacy_term()),
            KernelTermNode::FloatLiteral { carrier, bits } => {
                ScalarShape::Atom(MachineTerm::Constant {
                    format: *carrier,
                    bits: *bits,
                })
            }
            KernelTermNode::ThreadHandle(id) => ScalarShape::Atom(MachineTerm::ThreadHandle(*id)),
            KernelTermNode::ImportedScalar(input) => return Self::native(input.value()),
            _ => {
                if let Some(view) = float {
                    return Self::native(view.native_compat().expect("float atom key"));
                }
                if let Some(value) = root
                    .retained_machine_input()
                    .or_else(|| root.machine_read_leaf())
                {
                    return Self::native(value);
                }
                // Selected shapes without a key projection keep their written order.
                return Self::native(&KernelTermExport::machine(root).expect("machine key"));
            }
        })
    }
}
impl ScalarShape {
    fn rank(&self) -> u8 {
        match self {
            Self::WordBinary(..) => 2,
            Self::WordUnary(..) => 3,
            Self::If(..) => 4,
            Self::Fold(..) => 5,
            Self::Match(..) => 8,
            Self::Address(..) => 10,
            Self::IntegerConversion(..) => 11,
            Self::Cast(..) => 12,
            Self::BoolCast(..) => BOOL_CAST_RANK,
            Self::Application(..) => PURE_APPLICATION_RANK,
            Self::Call(..) => CLICK_APPLICATION_RANK,
            Self::Negate(false, _) => FLOAT32_NEGATE_RANK,
            Self::Binary(false, ..) => FLOAT32_BINARY_RANK,
            Self::Negate(true, _) => FLOAT64_NEGATE_RANK,
            Self::Binary(true, ..) => FLOAT64_BINARY_RANK,
            Self::Atom(value) => native_machine_rank(value),
        }
    }
}
impl Hash for ScalarStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl PartialEq for ScalarStorageKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.fingerprint == other.0.fingerprint && self.cmp(other).is_eq()
    }
}
impl Eq for ScalarStorageKey {}
impl PartialOrd for ScalarStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ScalarStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        enum Task<'a> {
            Term(&'a ScalarStorageKey, &'a ScalarStorageKey),
            Argument(&'a ArgumentKey, &'a ArgumentKey),
            Arm(&'a MatchArmKey, &'a MatchArmKey),
            Order(Ordering),
        }
        let mut pending = vec![Task::Term(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some(task) = pending.pop() {
            let (a, b) = match task {
                Task::Order(order) if !order.is_eq() => return order,
                Task::Order(_) => continue,
                Task::Argument(
                    ArgumentKey::Program(ProgramStorageKey::Scalar(at, a)),
                    ArgumentKey::Program(ProgramStorageKey::Scalar(bt, b)),
                ) if at == bt => (a, b),
                Task::Argument(a, b) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                    continue;
                }
                Task::Arm(a, b) => {
                    let order = (&a.variant, &a.bindings).cmp(&(&b.variant, &b.bindings));
                    if !order.is_eq() {
                        return order;
                    }
                    (&a.body, &b.body)
                }
                Task::Term(a, b) => (a, b),
            };
            if Arc::ptr_eq(&a.0, &b.0) || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let rank = a.0.shape.rank().cmp(&b.0.shape.rank());
            if !rank.is_eq() {
                return rank;
            }
            match (&a.0.shape, &b.0.shape) {
                (ScalarShape::Atom(a), ScalarShape::Atom(b)) => {
                    let cmp = a.cmp(b);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                }
                (ScalarShape::WordBinary(ao, af, a), ScalarShape::WordBinary(bo, bf, b)) => {
                    let order = (ao, af).cmp(&(bo, bf));
                    if !order.is_eq() {
                        return order;
                    }
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (ScalarShape::WordUnary(af, ao, a), ScalarShape::WordUnary(bf, bo, b)) => {
                    let order = (af, ao).cmp(&(bf, bo));
                    if !order.is_eq() {
                        return order;
                    }
                    pending.push(Task::Term(a, b));
                }
                (ScalarShape::If(ag, a), ScalarShape::If(bg, b)) => {
                    let order = ag.cmp(bg);
                    if !order.is_eq() {
                        return order;
                    }
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (ScalarShape::Fold(a, acc_a, item_a), ScalarShape::Fold(b, acc_b, item_b)) => {
                    // Start, end and initial precede both binders and the body.
                    pending.push(Task::Term(&a[3], &b[3]));
                    pending.push(Task::Order((acc_a, item_a).cmp(&(acc_b, item_b))));
                    pending.extend(
                        a[..3]
                            .iter()
                            .zip(&b[..3])
                            .rev()
                            .map(|(a, b)| Task::Term(a, b)),
                    );
                }
                (ScalarShape::Match(a, aa), ScalarShape::Match(b, ba)) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                    pending.push(Task::Order(aa.len().cmp(&ba.len())));
                    pending.extend(aa.iter().zip(ba).rev().map(|(a, b)| Task::Arm(a, b)));
                }
                (ScalarShape::Address(a), ScalarShape::Address(b)) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                }
                (ScalarShape::IntegerConversion(a, af), ScalarShape::IntegerConversion(b, bf)) => {
                    let order = (a, af).cmp(&(b, bf));
                    if !order.is_eq() {
                        return order;
                    }
                }
                (ScalarShape::Cast(ak, a, af, at), ScalarShape::Cast(bk, b, bf, bt)) => {
                    let order = ak.cmp(bk);
                    if !order.is_eq() {
                        return order;
                    }
                    // The written operand precedes the source and destination.
                    pending.push(Task::Order((af, at).cmp(&(bf, bt))));
                    pending.push(Task::Term(a, b));
                }
                (ScalarShape::BoolCast(af, a), ScalarShape::BoolCast(bf, b)) => {
                    let order = (af, a).cmp(&(bf, b));
                    if !order.is_eq() {
                        return order;
                    }
                }
                (ScalarShape::Negate(_, a), ScalarShape::Negate(_, b)) => {
                    pending.push(Task::Term(a, b))
                }
                (ScalarShape::Binary(_, ao, a), ScalarShape::Binary(_, bo, b)) => {
                    let cmp = ao.cmp(bo);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (ScalarShape::Application(an, a), ScalarShape::Application(bn, b)) => {
                    let cmp = an.cmp(bn);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.push(Task::Order(a.len().cmp(&b.len())));
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (ScalarShape::Call(an, a), ScalarShape::Call(bn, b)) => {
                    let cmp = an.cmp(bn);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.push(Task::Order(a.len().cmp(&b.len())));
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Argument(a, b)));
                }
                _ => unreachable!("same scalar key rank"),
            }
        }
        Ordering::Equal
    }
}

impl Drop for ScalarStorageKey {
    fn drop(&mut self) {
        fn take(key: &mut ScalarStorageKey, pending: &mut Vec<ScalarStorageKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0) {
                match std::mem::replace(
                    &mut data.shape,
                    ScalarShape::Atom(MachineTerm::constant(0)),
                ) {
                    ScalarShape::Negate(_, child)
                    | ScalarShape::WordUnary(_, _, child)
                    | ScalarShape::Cast(_, child, _, _) => pending.push(child),
                    ScalarShape::Binary(_, _, children)
                    | ScalarShape::WordBinary(_, _, children)
                    | ScalarShape::If(_, children) => pending.extend(children),
                    ScalarShape::Fold(children, ..) => pending.extend(children),
                    ScalarShape::Match(_, arms) => {
                        pending.extend(arms.into_iter().map(|arm| arm.body))
                    }
                    ScalarShape::Application(_, children) => pending.extend(children),
                    ScalarShape::Call(_, args) => {
                        for arg in args {
                            if let ArgumentKey::Program(ProgramStorageKey::Scalar(_, child)) = arg {
                                pending.push(child);
                            }
                        }
                    }
                    ScalarShape::Atom(_)
                    | ScalarShape::Address(_)
                    | ScalarShape::IntegerConversion(..)
                    | ScalarShape::BoolCast(..) => {}
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

fn has_scalar_key(root: &KernelTerm) -> bool {
    root.written_argument().is_none()
        && matches!(root.ty(), KernelType::Program(ty)
            if MachineIntegerType::from_program_type(*ty).is_some()
                || KernelFloatType::from_program_type(*ty).is_some())
}

thread_local! {
    static SCALAR_KEYS: std::cell::RefCell<crate::id_hash::U64Map<ScalarStorageKey>> = Default::default();
}
pub(super) fn clear_session_key_memos() {
    SCALAR_KEYS.with(|keys| keys.borrow_mut().clear());
}
pub(super) fn for_root(source: &KernelTerm) -> ScalarStorageKey {
    SCALAR_KEYS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(&root.id()) {
                continue;
            }
            if !finish {
                let children: Vec<_> = match root.node() {
                    KernelTermNode::FloatNegate { operand }
                    | KernelTermNode::MachineUnary { operand, .. }
                    | KernelTermNode::MachineCast { operand, .. }
                    | KernelTermNode::FloatConvert { operand, .. } => vec![operand],
                    KernelTermNode::FloatBinary { arguments, .. }
                    | KernelTermNode::MachineBinary { arguments, .. } => arguments.iter().collect(),
                    KernelTermNode::MachineIf { arguments } => arguments[1..].iter().collect(),
                    KernelTermNode::Fold(fold) => fold.arguments.iter().collect(),
                    KernelTermNode::Match(matched) => matched.arguments[1..].iter().collect(),
                    KernelTermNode::FloatCall(call) => call
                        .arguments
                        .iter()
                        .zip(&call.shared_machine_arguments)
                        .filter_map(|(child, carrier)| {
                            (carrier.is_none() && has_scalar_key(child)).then_some(child)
                        })
                        .collect(),
                    KernelTermNode::Call { arguments, .. } => arguments
                        .iter()
                        .filter(|child| has_scalar_key(child))
                        .collect(),
                    _ => Vec::new(),
                };
                if !children.is_empty() {
                    pending.push((root, true));
                    pending.extend(children.into_iter().rev().map(|child| (child, false)));
                    continue;
                }
            }
            let key = ScalarStorageKey::shared(root);
            keys.borrow_mut().insert(root.id(), key);
        }
        keys.borrow()
            .get(&source.id())
            .expect("scalar storage key")
            .clone()
    })
}
