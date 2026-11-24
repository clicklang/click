//! Native algebraic order projected onto shared children. Scalar fields and
//! opaque addresses keep selected descriptors until their storage slices.
use super::*;

#[derive(Clone, Debug)]
pub(in crate::kernel) struct AlgebraicStorageKey(Arc<Data>);
#[derive(Debug)]
struct Data {
    node: Node,
    fingerprint: u64,
}
#[derive(Debug, Hash)]
enum Node {
    Atom(Atom),
    List(Vec<AlgebraicStorageKey>),
}
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum Atom {
    Tag(u8),
    Type(AlgebraicType),
    Name(String),
    Variable(Variable),
    Argument(super::scalar::ArgumentKey),
    Program(ProgramStorageKey),
    Condition(ConditionStorageKey),
    Memory(ProgramPoint),
    Address(AddressKey),
}
impl AlgebraicStorageKey {
    fn new(node: Node) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        node.hash(&mut hash);
        Self(Arc::new(Data {
            node,
            fingerprint: hash.finish(),
        }))
    }
    fn atom(value: Atom) -> Self {
        Self::new(Node::Atom(value))
    }
    fn list(values: Vec<Self>) -> Self {
        Self::new(Node::List(values))
    }
    fn tag(value: u8) -> Self {
        Self::atom(Atom::Tag(value))
    }
    fn argument(root: &KernelTerm, carrier: Option<&SharedMachineIntegerTerm>) -> Self {
        use super::scalar::ArgumentKey;

        if let Some(carrier) = carrier {
            return Self::list(vec![
                Self::tag(1),
                Self::atom(Atom::Argument(ArgumentKey::SharedMachine(carrier.clone()))),
            ]);
        }
        if matches!(root.ty(), KernelType::Algebraic(_)) {
            return Self::list(vec![Self::tag(3), for_root(root)]);
        }
        if let KernelTermNode::ProgramParameter { operand } = root.node() {
            return Self::list(vec![
                Self::tag(0),
                Self::list(vec![Self::tag(16), for_root(operand)]),
            ]);
        }
        let (rank, payload) = match ArgumentKey::shared(root) {
            ArgumentKey::Program(value) => {
                let key = match value {
                    ProgramStorageKey::Algebraic(key) => Self::list(vec![Self::tag(16), key]),
                    value => Self::list(vec![
                        Self::tag(value.rank()),
                        Self::atom(Atom::Program(value)),
                    ]),
                };
                (0, key)
            }
            value @ ArgumentKey::SharedMachine(_) => (1, Self::atom(Atom::Argument(value))),
            value @ ArgumentKey::Integer(_) => (2, Self::atom(Atom::Argument(value))),
            value @ ArgumentKey::Array(..) => (4, Self::atom(Atom::Argument(value))),
            ArgumentKey::Algebraic(_) => unreachable!("algebraic child was projected"),
        };
        Self::list(vec![Self::tag(rank), payload])
    }
    pub(super) fn native_field(value: &AlgebraicValue) -> Self {
        Self::field(&KernelTermImport::for_exact_field_inputs().match_field(value))
    }
    pub(super) fn field(root: &KernelTerm) -> Self {
        // AlgebraicValue has Program / Integer / Algebraic order; call arguments
        // have an extra SharedMachine arm, whose original carrier is retained.
        let argument = Self::argument(root, None);
        let Node::List(parts) = &argument.0.node else {
            unreachable!()
        };
        let Node::Atom(Atom::Tag(rank)) = &parts[0].0.node else {
            unreachable!()
        };
        Self::list(vec![
            Self::tag(match rank {
                0 => 0,
                2 => 1,
                3 => 2,
                _ => unreachable!("algebraic field"),
            }),
            parts[1].clone(),
        ])
    }
    fn shared(root: &KernelTerm) -> Self {
        let KernelType::Algebraic(ty) = root.ty() else {
            unreachable!("algebraic key")
        };
        let mut parts = vec![Self::atom(Atom::Type(ty.clone()))];
        match root.node() {
            KernelTermNode::Variable(v) => {
                parts.extend([Self::tag(0), Self::atom(Atom::Variable(*v))])
            }
            KernelTermNode::Constructor(c) => parts.extend([
                Self::tag(1),
                Self::atom(Atom::Name(c.variant.clone())),
                Self::list(c.fields.iter().map(Self::field).collect()),
            ]),
            KernelTermNode::Match(m) => {
                let arms = m
                    .arms
                    .iter()
                    .zip(&m.arguments[1..])
                    .map(|(arm, body)| {
                        Self::list(vec![
                            Self::atom(Atom::Name(arm.variant.clone())),
                            Self::list(arm.bindings.iter().map(Self::field).collect()),
                            for_root(body),
                        ])
                    })
                    .collect();
                parts.extend([Self::tag(2), for_root(&m.arguments[0]), Self::list(arms)]);
            }
            KernelTermNode::AlgebraicCall(c) => parts.extend([
                Self::tag(3),
                Self::atom(Atom::Name(c.name.clone())),
                Self::list(
                    c.arguments
                        .iter()
                        .zip(&c.shared_machine_arguments)
                        .map(|(root, carrier)| Self::argument(root, carrier.as_ref()))
                        .collect(),
                ),
            ]),
            KernelTermNode::AlgebraicIf { arguments } => parts.extend([
                Self::tag(4),
                Self::atom(Atom::Condition(condition_for_root(&arguments[0]))),
                for_root(&arguments[1]),
                for_root(&arguments[2]),
            ]),
            KernelTermNode::AlgebraicRead(read) => {
                let (point, address) = read.parts();
                parts.extend([
                    Self::tag(5),
                    Self::atom(Atom::Memory(point.clone())),
                    Self::atom(Atom::Address(AddressKey::shared(address))),
                ]);
            }
            _ => unreachable!("algebraic key node"),
        }
        Self::list(parts)
    }
    pub(in crate::kernel) fn native(value: &AlgebraicTerm) -> Self {
        for_root(&KernelTermImport::for_exact_field_inputs().algebraic(value))
    }
}
impl Hash for AlgebraicStorageKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state)
    }
}
impl PartialEq for AlgebraicStorageKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.fingerprint == other.0.fingerprint && self.cmp(other).is_eq()
    }
}
impl Eq for AlgebraicStorageKey {}
impl PartialOrd for AlgebraicStorageKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for AlgebraicStorageKey {
    fn cmp(&self, other: &Self) -> Ordering {
        enum Task<'a> {
            Pair(&'a AlgebraicStorageKey, &'a AlgebraicStorageKey),
            End(Ordering),
        }
        let mut pending = vec![Task::Pair(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::End(order) if !order.is_eq() => return order,
                Task::End(_) => {}
                Task::Pair(a, b) => {
                    if Arc::ptr_eq(&a.0, &b.0)
                        || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0)))
                    {
                        continue;
                    }
                    crate::instrumentation::record_deterministic_work(1);
                    match (&a.0.node, &b.0.node) {
                        (Node::Atom(a), Node::Atom(b)) => {
                            let order = a.cmp(b);
                            if !order.is_eq() {
                                return order;
                            }
                        }
                        (Node::List(a), Node::List(b)) => {
                            pending.push(Task::End(a.len().cmp(&b.len())));
                            pending.extend(a.iter().zip(b).rev().map(|(a, b)| Task::Pair(a, b)));
                        }
                        _ => unreachable!("same native key position has the same grammar"),
                    }
                }
            }
        }
        Ordering::Equal
    }
}
impl Drop for AlgebraicStorageKey {
    fn drop(&mut self) {
        fn take(key: &mut AlgebraicStorageKey, pending: &mut Vec<AlgebraicStorageKey>) {
            if let Some(data) = Arc::get_mut(&mut key.0)
                && let Node::List(children) =
                    std::mem::replace(&mut data.node, Node::Atom(Atom::Tag(0)))
            {
                pending.extend(children);
            }
        }
        let mut pending = Vec::new();
        take(self, &mut pending);
        while let Some(mut key) = pending.pop() {
            take(&mut key, &mut pending);
        }
    }
}
thread_local! { static KEYS: std::cell::RefCell<crate::id_hash::U64Map<AlgebraicStorageKey>> = Default::default(); }
pub(super) fn clear_session_key_memos() {
    KEYS.with(|keys| keys.borrow_mut().clear());
}
fn dependencies(root: &KernelTerm) -> Vec<&KernelTerm> {
    let children: Vec<&KernelTerm> = match root.node() {
        KernelTermNode::Constructor(c) => c.fields.iter().collect(),
        KernelTermNode::AlgebraicCall(c) => c.arguments.iter().collect(),
        KernelTermNode::AlgebraicIf { arguments } => arguments[1..].iter().collect(),
        KernelTermNode::Match(m) => m
            .arguments
            .iter()
            .chain(m.arms.iter().flat_map(|arm| &arm.bindings))
            .collect(),
        _ => Vec::new(),
    };
    children
        .into_iter()
        .filter_map(|child| match child.node() {
            KernelTermNode::ProgramParameter { operand } => Some(operand),
            _ => matches!(child.ty(), KernelType::Algebraic(_)).then_some(child),
        })
        .collect()
}
pub(in crate::kernel) fn for_root(source: &KernelTerm) -> AlgebraicStorageKey {
    KEYS.with(|keys| {
        let mut pending = vec![(source, false)];
        while let Some((root, finish)) = pending.pop() {
            if keys.borrow().contains_key(&root.id()) {
                continue;
            }
            if !finish {
                pending.push((root, true));
                pending.extend(
                    dependencies(root)
                        .into_iter()
                        .rev()
                        .map(|child| (child, false)),
                );
            } else {
                let key = AlgebraicStorageKey::shared(root);
                keys.borrow_mut().insert(root.id(), key);
            }
        }
        keys.borrow()
            .get(&source.id())
            .expect("algebraic storage key")
            .clone()
    })
}
