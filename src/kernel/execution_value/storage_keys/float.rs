use super::*;

#[derive(Clone, Debug)]
pub(in crate::kernel) struct FloatStorageKey(Arc<FloatKeyData>);
#[derive(Debug)]
struct FloatKeyData {
    shape: FloatShape,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum FloatShape {
    Atom(MachineTerm),
    Negate(bool, FloatStorageKey),
    Binary(bool, FloatBinaryOperator, [FloatStorageKey; 2]),
    Application(String, Vec<FloatStorageKey>),
    Call(String, Vec<ArgumentKey>),
}
#[derive(Debug)]
enum ArgumentKey {
    Native(PureFunctionArgument),
    Float32(FloatStorageKey),
    Float64(FloatStorageKey),
}
impl ArgumentKey {
    fn native(value: &PureFunctionArgument) -> Self {
        match value {
            PureFunctionArgument::Value(ProgramValue::Float32(term)) => {
                Self::Float32(FloatStorageKey::native(term))
            }
            PureFunctionArgument::Value(ProgramValue::Float64(term)) => {
                Self::Float64(FloatStorageKey::native(term))
            }
            _ => Self::Native(value.clone()),
        }
    }
    fn rank(&self) -> (u8, u8) {
        match self {
            Self::Float32(_) => (0, 13),
            Self::Float64(_) => (0, 14),
            Self::Native(value) => match value {
                PureFunctionArgument::Value(v) => (0, native_rank(v)),
                PureFunctionArgument::SharedMachine(_) => (1, 0),
                PureFunctionArgument::Integer(_) => (2, 0),
                PureFunctionArgument::Algebraic(_) => (3, 0),
                PureFunctionArgument::ArrayRef { .. } => (4, 0),
            },
        }
    }
}
impl Hash for ArgumentKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rank().hash(state);
        match self {
            Self::Native(v) => v.hash(state),
            Self::Float32(v) | Self::Float64(v) => v.hash(state),
        }
    }
}
impl FloatStorageKey {
    fn new(shape: FloatShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(FloatKeyData {
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
            FloatArgument(bool),
        }
        let mut pending = vec![Task::Term(value)];
        let mut values = Vec::new();
        let mut arguments = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
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
                Task::Term(term) => values.push(Self::new(FloatShape::Atom(term.clone()))),
                Task::Argument(PureFunctionArgument::Value(ProgramValue::Float32(term))) => {
                    pending.push(Task::FloatArgument(false));
                    pending.push(Task::Term(term));
                }
                Task::Argument(PureFunctionArgument::Value(ProgramValue::Float64(term))) => {
                    pending.push(Task::FloatArgument(true));
                    pending.push(Task::Term(term));
                }
                Task::Argument(value) => arguments.push(ArgumentKey::Native(value.clone())),
                Task::FloatArgument(wide) => {
                    let value = values.pop().unwrap();
                    arguments.push(if wide {
                        ArgumentKey::Float64(value)
                    } else {
                        ArgumentKey::Float32(value)
                    });
                }
                Task::Negate(wide) => {
                    let value = values.pop().unwrap();
                    values.push(Self::new(FloatShape::Negate(wide, value)));
                }
                Task::Binary(wide, operator) => {
                    let b = values.pop().unwrap();
                    let a = values.pop().unwrap();
                    values.push(Self::new(FloatShape::Binary(wide, operator, [a, b])));
                }
                Task::Application(name, n) => {
                    let children = values.split_off(values.len() - n);
                    values.push(Self::new(FloatShape::Application(name.into(), children)));
                }
                Task::Call(name, n) => {
                    let children = arguments.split_off(arguments.len() - n);
                    values.push(Self::new(FloatShape::Call(name.into(), children)));
                }
            }
        }
        values.pop().expect("float key")
    }
    pub(in crate::kernel) fn shared(root: &KernelTerm) -> Self {
        let view = FloatOperandView::from_shared(root).expect("float key root");
        let wide = view.format() == KernelFloatType::Float64;
        Self::new(match root.node() {
            KernelTermNode::FloatNegate { operand } => {
                FloatShape::Negate(wide, operand.float_storage_key())
            }
            KernelTermNode::FloatBinary {
                operator,
                arguments,
            } => FloatShape::Binary(
                wide,
                *operator,
                arguments.each_ref().map(KernelTerm::float_storage_key),
            ),
            KernelTermNode::FloatConvert {
                source, operand, ..
            } => {
                let name = format!(
                    "c_{}_to_{}",
                    crate::kernel::program_type_spelling(*source),
                    crate::kernel::program_type_spelling(view.format().program_type())
                );
                let operand = if FloatOperandView::from_shared(operand).is_some() {
                    operand.float_storage_key()
                } else {
                    Self::native(
                        &KernelTermExport::machine(operand).expect("numeric conversion key"),
                    )
                };
                FloatShape::Application(name, vec![operand])
            }
            KernelTermNode::FloatCall(call) => {
                let arguments = call
                    .arguments
                    .iter()
                    .zip(&call.shared_machine_arguments)
                    .map(|(root, carrier)| {
                        if let Some(carrier) = carrier {
                            ArgumentKey::Native(PureFunctionArgument::SharedMachine(
                                carrier.clone(),
                            ))
                        } else if let Some(view) = FloatOperandView::from_shared(root) {
                            match view.format() {
                                KernelFloatType::Float32 => {
                                    ArgumentKey::Float32(root.float_storage_key())
                                }
                                KernelFloatType::Float64 => {
                                    ArgumentKey::Float64(root.float_storage_key())
                                }
                            }
                        } else {
                            ArgumentKey::native(
                                &KernelTermExport::default()
                                    .argument(root)
                                    .expect("selected call argument key"),
                            )
                        }
                    })
                    .collect();
                FloatShape::Call(call.name.clone(), arguments)
            }
            _ => return Self::native(view.native_compat().expect("float atom key")),
        })
    }
}
impl FloatShape {
    fn rank(&self) -> u8 {
        match self {
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
impl Hash for FloatStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl PartialEq for FloatStorageKey {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for FloatStorageKey {}
impl PartialOrd for FloatStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for FloatStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        enum Task<'a> {
            Term(&'a FloatStorageKey, &'a FloatStorageKey),
            Argument(&'a ArgumentKey, &'a ArgumentKey),
            Length(usize, usize),
        }
        let mut pending = vec![Task::Term(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some(task) = pending.pop() {
            let (a, b) = match task {
                Task::Length(a, b) => {
                    let cmp = a.cmp(&b);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    continue;
                }
                Task::Argument(a, b) => {
                    let cmp = a.rank().cmp(&b.rank());
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    match (a, b) {
                        (ArgumentKey::Native(a), ArgumentKey::Native(b)) => {
                            let cmp = a.cmp(b);
                            if !cmp.is_eq() {
                                return cmp;
                            }
                            continue;
                        }
                        (ArgumentKey::Float32(a), ArgumentKey::Float32(b))
                        | (ArgumentKey::Float64(a), ArgumentKey::Float64(b)) => (a, b),
                        _ => unreachable!("same argument rank"),
                    }
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
                (FloatShape::Atom(a), FloatShape::Atom(b)) => {
                    let cmp = a.cmp(b);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                }
                (FloatShape::Negate(_, a), FloatShape::Negate(_, b)) => {
                    pending.push(Task::Term(a, b))
                }
                (FloatShape::Binary(_, ao, a), FloatShape::Binary(_, bo, b)) => {
                    let cmp = ao.cmp(bo);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (FloatShape::Application(an, a), FloatShape::Application(bn, b)) => {
                    let cmp = an.cmp(bn);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.push(Task::Length(a.len(), b.len()));
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Term(a, b)));
                }
                (FloatShape::Call(an, a), FloatShape::Call(bn, b)) => {
                    let cmp = an.cmp(bn);
                    if !cmp.is_eq() {
                        return cmp;
                    }
                    pending.push(Task::Length(a.len(), b.len()));
                    pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Argument(a, b)));
                }
                _ => unreachable!("same float key rank"),
            }
        }
        Ordering::Equal
    }
}

impl Drop for FloatStorageKey {
    fn drop(&mut self) {
        fn take(key: &mut FloatStorageKey, pending: &mut Vec<FloatStorageKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0) {
                match std::mem::replace(&mut data.shape, FloatShape::Atom(MachineTerm::constant(0)))
                {
                    FloatShape::Negate(_, child) => pending.push(child),
                    FloatShape::Binary(_, _, children) => pending.extend(children),
                    FloatShape::Application(_, children) => pending.extend(children),
                    FloatShape::Call(_, args) => {
                        for arg in args {
                            match arg {
                                ArgumentKey::Float32(child) | ArgumentKey::Float64(child) => {
                                    pending.push(child)
                                }
                                ArgumentKey::Native(_) => {}
                            }
                        }
                    }
                    FloatShape::Atom(_) => {}
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

thread_local! {
    static FLOAT_KEYS: std::cell::RefCell<crate::id_hash::U64Map<FloatStorageKey>> = Default::default();
}
pub(super) fn clear_session_key_memos() {
    FLOAT_KEYS.with(|keys| keys.borrow_mut().clear());
}
pub(super) fn for_root(source: &KernelTerm) -> FloatStorageKey {
    FLOAT_KEYS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(&root.id()) {
                continue;
            }
            if !finish {
                let children: Vec<_> = match root.node() {
                    KernelTermNode::FloatNegate { operand } => vec![operand],
                    KernelTermNode::FloatBinary { arguments, .. } => arguments.iter().collect(),
                    KernelTermNode::FloatConvert { operand, .. }
                        if FloatOperandView::from_shared(operand).is_some() =>
                    {
                        vec![operand]
                    }
                    KernelTermNode::FloatCall(call) => call
                        .arguments
                        .iter()
                        .zip(&call.shared_machine_arguments)
                        .filter_map(|(child, carrier)| {
                            (carrier.is_none() && FloatOperandView::from_shared(child).is_some())
                                .then_some(child)
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                if !children.is_empty() {
                    pending.push((root, true));
                    pending.extend(children.into_iter().rev().map(|child| (child, false)));
                    continue;
                }
            }
            let key = FloatStorageKey::shared(root);
            keys.borrow_mut().insert(root.id(), key);
        }
        keys.borrow()
            .get(&source.id())
            .expect("float storage key")
            .clone()
    })
}
