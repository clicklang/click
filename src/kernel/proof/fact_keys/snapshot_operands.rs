//! Interned snapshot-blind operand keys. Child keys compare by identity,
//! so shared arithmetic never expands into recursive boxed index keys.
use super::*;
use std::sync::{Mutex, OnceLock};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Node {
    Load(Box<SnapshotBlindPointerKey>, LoadKind),
    Address(Box<SnapshotBlindPointerKey>),
    Binary(
        BitvectorBinaryOp,
        SnapshotBlindBitvectorKey,
        SnapshotBlindBitvectorKey,
    ),
    Unary(BitvectorUnaryOp, SnapshotBlindBitvectorKey),
    If(
        Box<SnapshotBlindConditionKey>,
        SnapshotBlindBitvectorKey,
        SnapshotBlindBitvectorKey,
    ),
    Exact(MachineTerm),
}

struct Record {
    id: u64,
    fingerprint: u64,
    node: Node,
    checked_match: bool,
}
#[derive(Clone)]
pub(crate) struct SnapshotBlindBitvectorKey(Arc<Record>);
impl fmt::Debug for SnapshotBlindBitvectorKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SnapshotBlindBitvectorKey")
            .field(&self.0.id)
            .finish()
    }
}
impl PartialEq for SnapshotBlindBitvectorKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for SnapshotBlindBitvectorKey {}
impl PartialOrd for SnapshotBlindBitvectorKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SnapshotBlindBitvectorKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.id.cmp(&other.0.id)
    }
}
impl Hash for SnapshotBlindBitvectorKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}
impl SnapshotBlindBitvectorKey {
    pub(super) fn requires_checked_match(&self) -> bool {
        self.0.checked_match
    }
}

type Interner = HashMap<u64, Vec<Weak<Record>>>;
fn interner() -> &'static Mutex<Interner> {
    static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
    INTERNER.get_or_init(Mutex::default)
}
impl Drop for Record {
    fn drop(&mut self) {
        let Ok(mut table) = interner().try_lock() else {
            return;
        };
        if let Some(bucket) = table.get_mut(&self.fingerprint) {
            bucket.retain(|entry| entry.strong_count() != 0);
            if bucket.is_empty() {
                table.remove(&self.fingerprint);
            }
        }
    }
}
fn intern(node: Node) -> SnapshotBlindBitvectorKey {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT_ID: AtomicU64 = AtomicU64::new(1);
    crate::instrumentation::record_deterministic_work(1);
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    node.hash(&mut hash);
    let fingerprint = hash.finish();
    let mut table = interner().lock().expect("snapshot operand interner");
    let bucket = table.entry(fingerprint).or_default();
    let found = bucket
        .iter()
        .filter_map(Weak::upgrade)
        .find(|record| record.node == node);
    if let Some(record) = found {
        return SnapshotBlindBitvectorKey(record);
    }
    bucket.retain(|entry| entry.strong_count() != 0);
    let checked_match = match &node {
        Node::Load(..) | Node::Address(..) => true,
        Node::Binary(_, a, b) => a.requires_checked_match() || b.requires_checked_match(),
        Node::Unary(_, a) => a.requires_checked_match(),
        Node::If(c, a, b) => {
            c.requires_checked_match() || a.requires_checked_match() || b.requires_checked_match()
        }
        Node::Exact(_) => false,
    };
    let record = Arc::new(Record {
        id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
        fingerprint,
        node,
        checked_match,
    });
    bucket.push(Arc::downgrade(&record));
    SnapshotBlindBitvectorKey(record)
}

pub(super) fn written(term: &MachineTerm) -> SnapshotBlindBitvectorKey {
    let node = match term {
        MachineTerm::PointerAddress(pointer, _) => {
            Node::Address(Box::new(snapshot_blind_pointer_key(pointer)))
        }
        MachineTerm::MemoryLoad(_, pointer, kind) => {
            Node::Load(Box::new(snapshot_blind_pointer_key(pointer)), *kind)
        }
        MachineTerm::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            match (
                crate::kernel::registered_load_for_variable(variable),
                crate::kernel::registered_load_kind_for_variable(variable),
            ) {
                (Some((_, pointer)), Some(kind)) => {
                    Node::Load(Box::new(snapshot_blind_pointer_key(&pointer)), kind)
                }
                _ => Node::Exact(term.clone()),
            }
        }
        // Keep the existing opaque If boundary for Integer and Bool
        // predicates; only top-level machine observations have a key view.
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } if !matches!(
            condition.as_ref(),
            crate::kernel::integer_comparison_condition!(_, _)
        ) && !condition.is_bool_value_form() =>
        {
            Node::If(
                Box::new(snapshot_blind_condition_key(condition)),
                snapshot_blind_bitvector_key(then_term),
                snapshot_blind_bitvector_key(else_term),
            )
        }
        term => {
            if let Some((operator, left, right)) = term.as_binary() {
                Node::Binary(
                    operator,
                    snapshot_blind_bitvector_key(left),
                    snapshot_blind_bitvector_key(right),
                )
            } else if let Some((operator, value)) = term.as_unary() {
                Node::Unary(operator, snapshot_blind_bitvector_key(value))
            } else {
                Node::Exact(term.clone())
            }
        }
    };
    intern(node)
}

thread_local! {
    static SHARED_KEYS: std::cell::RefCell<HashMap<u64, SnapshotBlindBitvectorKey>> = Default::default();
}

pub(super) fn clear() {
    SHARED_KEYS.with(|memo| memo.borrow_mut().clear());
}

pub(super) fn operand(view: crate::kernel::MachineOperandView<'_>) -> SnapshotBlindBitvectorKey {
    use crate::kernel::MachineOperandView as V;
    let V::Shared(root) = view else {
        let V::Legacy(term) = view else {
            unreachable!()
        };
        return written(term);
    };
    let get = |root: &crate::kernel::KernelTerm| {
        SHARED_KEYS.with(|memo| memo.borrow().get(&root.id()).cloned())
    };
    let mut pending = vec![(root.clone(), false)];
    while let Some((root, finish)) = pending.pop() {
        if get(&root).is_some() {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let view = V::Shared(&root);
        let children = if let Some((_, _, children)) = view.binary() {
            children.into_iter().collect::<Vec<_>>()
        } else if let Some((_, _, _, child)) = view.cast() {
            vec![child]
        } else if let Some((_, _, child)) = view.unary() {
            vec![child]
        } else {
            Vec::new()
        };
        if !finish && !children.is_empty() {
            pending.push((root.clone(), true));
            for child in children.into_iter().rev() {
                let V::Shared(child) = child else {
                    unreachable!()
                };
                if get(child).is_none() {
                    pending.push((child.clone(), false));
                }
            }
            continue;
        }
        let child_key = |child| {
            let V::Shared(child) = child else {
                unreachable!()
            };
            get(child).expect("keyed child")
        };
        let key = if let Some(value) = root.machine_conversion_leaf() {
            written(value)
        } else if let Some(variable) = view.variable() {
            written(&MachineTerm::Variable(*variable))
        } else if let Some(literal) = view.literal() {
            intern(Node::Exact(literal))
        } else if let Some((format, op, [a, b])) = view.binary() {
            intern(Node::Binary(
                BitvectorBinaryOp::Machine(format, op),
                child_key(a),
                child_key(b),
            ))
        } else if let Some((encoding, source, destination, child)) = view.cast() {
            intern(Node::Unary(
                encoding.unary(source, destination),
                child_key(child),
            ))
        } else if let Some((format, op, child)) = view.unary() {
            intern(Node::Unary(
                BitvectorUnaryOp::Machine(format, op),
                child_key(child),
            ))
        } else {
            unreachable!("shared machine operand fragment")
        };
        SHARED_KEYS.with(|memo| memo.borrow_mut().insert(root.id(), key));
    }
    get(root).expect("keyed root")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp,
        MachineOperandView as V,
    };

    #[test]
    fn shared_snapshot_operand_keys_match_written_structure_without_export() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
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
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
            ] {
                let native = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(MachineTerm::Variable(Variable(998201))),
                    right: Box::new(MachineTerm::Variable(Variable(998202))),
                };
                let shared = KernelTermImport::default()
                    .machine_arithmetic(format, &native)
                    .unwrap();
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(operand(V::Shared(&shared)), written(&native));
                assert!(!operand(V::Shared(&shared)).requires_checked_match());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[test]
    fn observation_keys_select_native_load_candidates_without_proving_them() {
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block("snapshot-comparison", 4),
        );
        let pointer = Pointer {
            block: "snapshot-comparison".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
            &memory,
        );
        let format = MachineIntegerType::Int32;
        let native = MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(MachineTerm::constant(1)),
        };
        let shared = KernelTermImport::default()
            .machine_arithmetic(format, &native)
            .unwrap();
        let limit = MachineTerm::constant(20);
        for relation in [
            CompareRelation::Equal,
            CompareRelation::LessThan,
            CompareRelation::LessEqual,
        ] {
            let native = Proposition::ConditionIs(
                ConditionTerm::machine_compare(format, relation, native.clone(), limit.clone()),
                true,
            );
            let exports = KernelTermExport::machine_export_count();
            let shared = Proposition::ConditionIs(
                condition_for_operand_views(
                    format,
                    relation,
                    [V::Shared(&shared), V::Legacy(&limit)],
                ),
                true,
            );
            let key = snapshot_blind_proposition_key(&shared);
            assert_eq!(key, snapshot_blind_proposition_key(&native));
            assert!(key.requires_checked_match());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn snapshot_operand_memo_tracks_restored_load_registries() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = crate::kernel::eval::capture_load_variable_registry();
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block("snapshot-key", 4),
        );
        let pointer = Pointer {
            block: "snapshot-key".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
            &memory,
        );
        let loaded = crate::kernel::eval::capture_load_variable_registry();
        let shared = KernelTerm::variable(KernelType::C(CType::Int32), variable);
        let key = operand(V::Shared(&shared));
        assert!(key.requires_checked_match());
        assert_eq!(
            key,
            written(&MachineTerm::MemoryLoad(
                memory,
                Box::new(pointer),
                LoadKind::Int32
            ))
        );
        crate::kernel::eval::restore_load_variable_registry(&empty);
        let unregistered = operand(V::Shared(&shared));
        assert_ne!(key, unregistered);
        assert!(!unregistered.requires_checked_match());
        crate::kernel::eval::restore_load_variable_registry(&loaded);
        assert_eq!(key, operand(V::Shared(&shared)));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/snapshot_operands/tests.rs");
}
