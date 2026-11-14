//! Prepared offset nodes. Construction preserves written shape, scale and
//! interpretation; it neither normalizes offsets nor consults facts.
use super::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum KernelPointerOffset {
    Constant(i64),
    Variable(Variable),
    Add([SharedPointerOffset; 2]),
    Int32Scaled {
        value: KernelTerm,
        byte_width: i64,
    },
    Int64Scaled {
        value: KernelTerm,
        byte_width: i64,
        unsigned: bool,
    },
}

/// Shared internal address component. Numeric children are common KernelTerm
/// handles; offsets are not independently spellable Click values.
#[derive(Clone)]
pub(crate) struct SharedPointerOffset(Arc<OffsetData>);
struct OffsetData {
    id: u64,
    node: KernelPointerOffset,
}
impl std::fmt::Debug for SharedPointerOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SharedPointerOffset")
            .field(&self.0.id)
            .finish()
    }
}
impl PartialEq for SharedPointerOffset {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for SharedPointerOffset {}
impl Hash for SharedPointerOffset {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}
#[derive(Default)]
struct OffsetInterner {
    nodes: HashMap<KernelPointerOffset, Weak<OffsetData>>,
    cleanup: VecDeque<KernelPointerOffset>,
    next_id: u64,
}
impl SharedPointerOffset {
    pub(crate) fn node(&self) -> &KernelPointerOffset {
        &self.0.node
    }
    fn intern(node: KernelPointerOffset) -> Self {
        static INTERNER: std::sync::OnceLock<Mutex<OffsetInterner>> = std::sync::OnceLock::new();
        let mut interner = INTERNER
            .get_or_init(Default::default)
            .lock()
            .expect("offset interner");
        // As with the common term arena, bounded upkeep never scans the arena.
        for _ in 0..interner.cleanup.len().min(8) {
            let key = interner.cleanup.pop_front().unwrap();
            if interner
                .nodes
                .get(&key)
                .is_some_and(|value| value.strong_count() == 0)
            {
                interner.nodes.remove(&key);
            } else {
                interner.cleanup.push_back(key);
            }
        }
        if let Some(value) = interner.nodes.get(&node).and_then(Weak::upgrade) {
            return Self(value);
        }
        let id = interner.next_id;
        interner.next_id = id.checked_add(1).expect("offset identity exhausted");
        let value = Arc::new(OffsetData {
            id,
            node: node.clone(),
        });
        interner.nodes.insert(node.clone(), Arc::downgrade(&value));
        interner.cleanup.push_back(node);
        Self(value)
    }
}

impl KernelPointerOffset {
    pub(crate) fn offset_children(&self) -> &[SharedPointerOffset] {
        match self {
            Self::Add(children) => children,
            _ => &[],
        }
    }

    pub(crate) fn index(&self) -> Option<&KernelTerm> {
        match self {
            Self::Int32Scaled { value, .. } | Self::Int64Scaled { value, .. } => Some(value),
            _ => None,
        }
    }

    pub(crate) fn into_shared(self) -> Result<SharedPointerOffset, &'static str> {
        // One node plus bounded arena upkeep. Charge its fixed allowance so
        // an unrelated arena population cannot change deterministic work.
        crate::instrumentation::record_deterministic_work(9);
        match &self {
            Self::Int32Scaled { value, .. }
                if !matches!(
                    value.ty(),
                    KernelType::Program(ProgramType::Int32 | ProgramType::UInt32)
                ) =>
            {
                return Err("32-bit offset index has the wrong type");
            }
            // The interpretation flag is independent of the retained index carrier.
            Self::Int64Scaled { value, .. }
                if !matches!(
                    value.ty(),
                    KernelType::Program(ProgramType::Int64 | ProgramType::UInt64)
                ) =>
            {
                return Err("64-bit offset index has the wrong type");
            }
            _ => {}
        }
        Ok(SharedPointerOffset::intern(self))
    }

    pub(crate) fn import(offset: &PointerOffsetTerm) -> SharedPointerOffset {
        enum Task<'a> {
            Enter(&'a PointerOffsetTerm),
            Add,
        }
        let mut pending = vec![Task::Enter(offset)];
        let mut values = Vec::new();
        let index = |value: &SharedMachineIntegerTerm| {
            value.shared_operand().cloned().unwrap_or_else(|| {
                KernelTerm::retained_native_machine_operand(value.ty(), value.structural_value())
            })
        };
        while let Some(task) = pending.pop() {
            let node = match task {
                Task::Enter(PointerOffsetTerm::Constant(value)) => Self::Constant(*value),
                Task::Enter(PointerOffsetTerm::Variable(value)) => Self::Variable(*value),
                Task::Enter(PointerOffsetTerm::Add(left, right)) => {
                    pending.extend([Task::Add, Task::Enter(right), Task::Enter(left)]);
                    continue;
                }
                Task::Enter(PointerOffsetTerm::Int32Scaled { value, byte_width }) => {
                    Self::Int32Scaled {
                        value: index(value),
                        byte_width: *byte_width,
                    }
                }
                Task::Enter(PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                }) => Self::Int64Scaled {
                    value: index(value),
                    byte_width: *byte_width,
                    unsigned: *unsigned,
                },
                Task::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    Self::Add([left, right])
                }
            };
            values.push(node.into_shared().expect("native offset types"));
        }
        values.pop().expect("offset root")
    }

    /// Explicit native output. Completed offset children are moved, never
    /// cached and cloned at every prefix. Shared numeric indices stay shared.
    pub(crate) fn export(root: &SharedPointerOffset) -> Result<PointerOffsetTerm, &'static str> {
        enum Task<'a> {
            Enter(&'a SharedPointerOffset),
            Add,
        }
        let mut pending = vec![Task::Enter(root)];
        let mut values = Vec::new();
        let index = |value: &KernelTerm| {
            let KernelType::Program(ty) = value.ty() else {
                return Err("expected machine offset index");
            };
            let format = MachineIntegerType::from_program_type(*ty)
                .ok_or("expected machine offset index")?;
            if let KernelTermNode::Legacy(payload) = value.node()
                && let Some(native) = payload.machine_operand()
            {
                return Ok(SharedMachineIntegerTerm::index(format, native.clone()));
            }
            if let Some(value) = SharedMachineIntegerTerm::from_shared(format, value.clone()) {
                return Ok(value);
            }
            // This is explicit native output, not an implicit checker read.
            KernelTermExport::machine(value)
                .map(|native| SharedMachineIntegerTerm::index(format, native))
        };
        while let Some(task) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let value = match task {
                Task::Enter(root) => match root.node() {
                    Self::Constant(value) => PointerOffsetTerm::Constant(*value),
                    Self::Variable(value) => PointerOffsetTerm::Variable(*value),
                    Self::Add([left, right]) => {
                        pending.extend([Task::Add, Task::Enter(right), Task::Enter(left)]);
                        continue;
                    }
                    Self::Int32Scaled { value, byte_width } => PointerOffsetTerm::Int32Scaled {
                        value: index(value)?,
                        byte_width: *byte_width,
                    },
                    Self::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => PointerOffsetTerm::Int64Scaled {
                        value: index(value)?,
                        byte_width: *byte_width,
                        unsigned: *unsigned,
                    },
                },
                Task::Add => {
                    let right = values.pop().ok_or("missing right offset")?;
                    let left = values.pop().ok_or("missing left offset")?;
                    PointerOffsetTerm::Add(Box::new(left), Box::new(right))
                }
            };
            values.push(value);
        }
        values.pop().ok_or("missing offset root")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_payload_round_trips_shape_scale_and_interpretation() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut values = vec![
            PointerOffsetTerm::Constant(i64::MIN),
            PointerOffsetTerm::Constant(i64::MAX),
            PointerOffsetTerm::Variable(Variable(994001)),
        ];
        for width in [0, -8, 4] {
            values.push(PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(994002)),
                width,
            ));
            for unsigned in [false, true] {
                values.push(PointerOffsetTerm::scaled_int64_node(
                    MachineTerm::Variable(Variable(994003)),
                    width,
                    unsigned,
                ));
            }
        }
        for value in values {
            let source =
                PointerOffsetTerm::Add(Box::new(PointerOffsetTerm::Constant(0)), Box::new(value));
            let root = KernelPointerOffset::import(&source);
            assert_eq!(KernelPointerOffset::export(&root).unwrap(), source);
            assert_eq!(KernelPointerOffset::import(&source), root);
            assert_eq!(root.node().offset_children().len(), 2);
        }
        let signed = PointerOffsetTerm::scaled_int64_node(
            MachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            false,
        );
        let unsigned = PointerOffsetTerm::scaled_int64_node(
            MachineTerm::Constant {
                format: MachineIntegerType::Int64,
                bits: u64::MAX as u128,
            },
            1,
            true,
        );
        assert_ne!(
            KernelPointerOffset::import(&signed),
            KernelPointerOffset::import(&unsigned)
        );
    }

    #[test]
    fn offset_payload_preserves_the_index_carrier_independently_of_interpretation() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let value =
                SharedMachineIntegerTerm::index(format, MachineTerm::Variable(Variable(994006)));
            let source = if format.format().bits() == 32 {
                PointerOffsetTerm::Int32Scaled {
                    value: value.clone(),
                    byte_width: 4,
                }
            } else {
                PointerOffsetTerm::Int64Scaled {
                    value: value.clone(),
                    byte_width: 8,
                    unsigned: false,
                }
            };
            let root = KernelPointerOffset::import(&source);
            let output = KernelPointerOffset::export(&root).unwrap();
            assert_eq!(source, output);
            let index = root.node().index().unwrap();
            assert_eq!(index.ty(), &KernelType::Program(format.program_type()));
            assert_eq!(index, value.shared_operand().unwrap());
        }
    }

    #[test]
    fn offset_payload_keeps_exact_opaque_index_annotations() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        let _session = crate::kernel::VerificationSession::enter();
        let mut roots = Vec::new();
        let mut natives = Vec::new();
        for class in [CScalarClass::Int, CScalarClass::Char] {
            let expected = Some(CAccessClass::Scalar(class));
            let source = PointerOffsetTerm::scaled_int64_node(
                MachineTerm::PointerAddress(
                    Box::new(Pointer::symbolic(Variable(994004))),
                    crate::kernel::AddressObjectClass::new(expected.clone()),
                ),
                1,
                true,
            );
            let root = KernelPointerOffset::import(&source);
            let output = KernelPointerOffset::export(&root).unwrap();
            assert_eq!(source, output);
            let PointerOffsetTerm::Int64Scaled { value, .. } = output else {
                panic!("scaled index")
            };
            let MachineTerm::PointerAddress(_, annotation) = value.structural_value() else {
                panic!("exact address input")
            };
            assert_eq!(annotation.class(), expected);
            roots.push(root);
            natives.push(source);
        }
        assert_eq!(natives[0], natives[1]);
        assert_ne!(roots[0], roots[1]);
    }

    #[test]
    fn offset_payload_rejects_mixed_sorts_without_normalizing_children() {
        let offset = KernelPointerOffset::Constant(0).into_shared().unwrap();
        let integer = KernelTerm::integer_literal(0.into());
        assert!(
            KernelPointerOffset::Int32Scaled {
                value: integer,
                byte_width: 0
            }
            .into_shared()
            .is_err()
        );
        let wide = KernelTerm::variable(KernelType::Program(ProgramType::Int64), Variable(994005));
        assert!(
            KernelPointerOffset::Int32Scaled {
                value: wide,
                byte_width: 1
            }
            .into_shared()
            .is_err()
        );
        let sum = KernelPointerOffset::Add([offset.clone(), offset.clone()])
            .into_shared()
            .unwrap();
        assert_ne!(sum, offset);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term/offsets.rs");
}
