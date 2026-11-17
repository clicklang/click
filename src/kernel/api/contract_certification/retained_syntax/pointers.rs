//! Borrow exact pointer payloads and written addresses during certification.
use super::*;
use crate::kernel::{
    KernelPointerOffset, Pointer, PointerBlock, PointerOffsetTerm, PointerValue,
    RetainedPointerMetadata, SharedPointerAddress, SharedPointerOffset, SharedPointerValue,
};
use std::borrow::Cow;

#[derive(Clone, Copy)]
enum Address<'a> {
    Native(&'a Pointer),
    Shared(&'a SharedPointerAddress),
}
impl<'a> Address<'a> {
    fn parts(self) -> (&'a PointerBlock, Offset<'a>) {
        match self {
            Self::Native(value) => (&value.block, Offset::Native(&value.offset)),
            Self::Shared(value) => (
                value.node().block.native_atom(),
                Offset::Shared(&value.node().offset),
            ),
        }
    }
}

#[derive(Clone, Copy)]
enum Offset<'a> {
    Native(&'a PointerOffsetTerm),
    Shared(&'a SharedPointerOffset),
}
enum OffsetNode<'a> {
    Constant(i64),
    Variable(Variable),
    Add([Offset<'a>; 2]),
    Scaled {
        wide: bool,
        unsigned: bool,
        byte_width: i64,
        ty: MachineIntegerType,
        value: Operand<'a>,
    },
}
impl<'a> Offset<'a> {
    fn node(self) -> Option<OffsetNode<'a>> {
        use KernelPointerOffset as K;
        use OffsetNode as V;
        use PointerOffsetTerm as P;
        let shared_index = |value: &'a KernelTerm| {
            let KernelType::Program(ty) = value.ty() else {
                return None;
            };
            let ty = MachineIntegerType::from_program_type(*ty)?;
            // The native offset exporter preserves opaque index payloads as
            // native operands. Do not grant them shared-root identity here.
            let operand = if matches!(value.node(), N::Legacy(_)) {
                Operand::Legacy(value.machine_conversion_leaf()?)
            } else {
                Operand::Shared(value)
            };
            Some((ty, operand))
        };
        Some(match self {
            Self::Native(P::Constant(value)) => V::Constant(*value),
            Self::Native(P::Variable(value)) => V::Variable(*value),
            Self::Native(P::Add(a, b)) => V::Add([Self::Native(a), Self::Native(b)]),
            Self::Native(P::Int32Scaled { value, byte_width }) => V::Scaled {
                wide: false,
                unsigned: false,
                byte_width: *byte_width,
                ty: value.ty(),
                value: value.operand_view(),
            },
            Self::Native(P::Int64Scaled {
                value,
                byte_width,
                unsigned,
            }) => V::Scaled {
                wide: true,
                unsigned: *unsigned,
                byte_width: *byte_width,
                ty: value.ty(),
                value: value.operand_view(),
            },
            Self::Shared(value) => match value.node() {
                K::Constant(value) => V::Constant(*value),
                K::Variable(value) => V::Variable(*value),
                K::Add([a, b]) => V::Add([Self::Shared(a), Self::Shared(b)]),
                K::Int32Scaled { value, byte_width } => {
                    let (ty, value) = shared_index(value)?;
                    V::Scaled {
                        wide: false,
                        unsigned: false,
                        byte_width: *byte_width,
                        ty,
                        value,
                    }
                }
                K::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let (ty, value) = shared_index(value)?;
                    V::Scaled {
                        wide: true,
                        unsigned: *unsigned,
                        byte_width: *byte_width,
                        ty,
                        value,
                    }
                }
            },
        })
    }
}

#[derive(Clone, Copy)]
enum Value<'a> {
    Native(&'a PointerValue),
    Shared(&'a SharedPointerValue),
}
impl<'a> Value<'a> {
    fn argument(argument: CallArgument<'a>) -> Option<Self> {
        match argument {
            CallArgument::Native(A::Value(ProgramValue::Pointer(value))) => {
                Some(Self::Native(value))
            }
            CallArgument::Shared(root) => root.pointer_payload().map(Self::Shared),
            _ => None,
        }
    }
    fn metadata(self) -> RetainedPointerMetadata<'a> {
        match self {
            Self::Native(value) => value.retained_nonaddress_metadata(),
            Self::Shared(value) => value.retained_nonaddress_metadata(),
        }
    }
    fn address(self) -> Address<'a> {
        match self {
            Self::Native(value) => Address::Native(value.pointer()),
            Self::Shared(value) => Address::Shared(&value.node().address),
        }
    }
    fn provenance(self) -> Address<'a> {
        match self {
            Self::Native(value) => Address::Native(value.provenance()),
            Self::Shared(value) => Address::Shared(&value.node().provenance),
        }
    }
    fn opaque_extent(self) -> Option<Address<'a>> {
        match self {
            Self::Native(value) => value.opaque_extent().map(Address::Native),
            Self::Shared(value) => value.node().opaque_extent.as_ref().map(Address::Shared),
        }
    }
    fn extent(self) -> Option<(Address<'a>, Operand<'a>)> {
        match self {
            Self::Native(value) => value.extent().map(|extent| {
                (
                    Address::Native(&extent.start),
                    Operand::Legacy(&extent.width),
                )
            }),
            Self::Shared(value) => {
                value
                    .node()
                    .qualifiers
                    .as_ref()?
                    .extent
                    .as_ref()
                    .map(|extent| {
                        (
                            Address::Shared(&extent.start),
                            Operand::Shared(&extent.width),
                        )
                    })
            }
        }
    }
}

struct Array<'a> {
    memory: (u32, u32),
    element_type: ProgramType,
    pointer: Value<'a>,
}
impl<'a> Array<'a> {
    fn argument(argument: CallArgument<'a>) -> Option<Self> {
        match argument {
            CallArgument::Native(A::ArrayRef {
                memory,
                pointer: ProgramValue::Pointer(pointer),
                element_type,
            }) => Some(Self {
                memory: crate::kernel::intern_memory_ref(memory).arena_id(),
                element_type: *element_type,
                pointer: Value::Native(pointer),
            }),
            CallArgument::Shared(root) => {
                let N::ArrayReference {
                    memory,
                    pointer,
                    element_type,
                } = root.node()
                else {
                    return None;
                };
                Some(Self {
                    memory: memory.arena_id(),
                    element_type: *element_type,
                    pointer: Value::Shared(pointer.pointer_payload()?),
                })
            }
            _ => None,
        }
    }
}

impl Comparison {
    pub(super) fn pointer_arguments(
        &mut self,
        left: CallArgument<'_>,
        right: CallArgument<'_>,
    ) -> Option<bool> {
        match (Value::argument(left), Value::argument(right)) {
            (Some(a), Some(b)) => return Some(self.pointer_values(a, b)),
            (Some(_), None) | (None, Some(_)) => return Some(false),
            (None, None) => {}
        }
        match (Array::argument(left), Array::argument(right)) {
            (Some(a), Some(b)) => Some(
                a.memory == b.memory
                    && a.element_type == b.element_type
                    && self.pointer_values(a.pointer, b.pointer),
            ),
            (Some(_), None) | (None, Some(_)) => Some(false),
            (None, None) => None,
        }
    }
    pub(super) fn pointer(&mut self, a: &Pointer, b: &Pointer) -> bool {
        self.addresses(Address::Native(a), Address::Native(b))
    }
    pub(super) fn shared_addresses(
        &mut self,
        a: &SharedPointerAddress,
        b: &SharedPointerAddress,
    ) -> bool {
        self.addresses(Address::Shared(a), Address::Shared(b))
    }
    pub(super) fn pointer_value(&mut self, a: &PointerValue, b: &PointerValue) -> bool {
        self.pointer_values(Value::Native(a), Value::Native(b))
    }
    fn pointer_values(&mut self, a: Value<'_>, b: Value<'_>) -> bool {
        if a.metadata() != b.metadata()
            || !self.addresses(a.address(), b.address())
            || !self.addresses(a.provenance(), b.provenance())
        {
            return false;
        }
        match (a.opaque_extent(), b.opaque_extent()) {
            (Some(a), Some(b)) if self.addresses(a, b) => {}
            (None, None) => {}
            _ => return false,
        }
        match (a.extent(), b.extent()) {
            (Some((ap, aw)), Some((bp, bw))) => {
                if !self.addresses(ap, bp) {
                    return false;
                }
                // Extent widths have an existing native-syntax admission rule.
                // Export only this selected width, never the complete pointer;
                // a shared identity shortcut would admit additional widths.
                let native = |value| match value {
                    Operand::Legacy(value) => Cow::Borrowed(value),
                    Operand::Shared(root) => Cow::Owned(
                        crate::kernel::KernelTermExport::machine(root).expect("extent width"),
                    ),
                };
                let (aw, bw) = (native(aw), native(bw));
                self.machine(Operand::Legacy(&aw), Operand::Legacy(&bw))
            }
            (None, None) => true,
            _ => false,
        }
    }
    fn addresses(&mut self, a: Address<'_>, b: Address<'_>) -> bool {
        use OffsetNode as O;
        let ((ab, ao), (bb, bo)) = (a.parts(), b.parts());
        let blocks = match (ab, bb) {
            (
                PointerBlock::PureFunctionApplication(a),
                PointerBlock::PureFunctionApplication(b),
            ) => {
                a.name() == b.name()
                    && a.arguments().len() == b.arguments().len()
                    && a.arguments()
                        .iter()
                        .zip(b.arguments())
                        .all(|(a, b)| self.argument(a, b))
            }
            _ => ab == bb,
        };
        if !blocks {
            return false;
        }
        let mut pending = vec![(ao, bo)];
        let mut seen = HashSet::new();
        while let Some((a, b)) = pending.pop() {
            // Memoize completed structure pairs without granting identity to
            // an unsupported scaled index on its first visit.
            if let (Offset::Shared(a), Offset::Shared(b)) = (a, b)
                && !seen.insert((a, b))
            {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            match (a.node(), b.node()) {
                (Some(O::Constant(a)), Some(O::Constant(b))) if a == b => {}
                (Some(O::Variable(a)), Some(O::Variable(b))) if a == b => {}
                (Some(O::Add(a)), Some(O::Add(b))) => pending.extend(a.into_iter().zip(b)),
                (
                    Some(O::Scaled {
                        wide: aw,
                        unsigned: au,
                        byte_width: ab,
                        ty: at,
                        value: av,
                    }),
                    Some(O::Scaled {
                        wide: bw,
                        unsigned: bu,
                        byte_width: bb,
                        ty: bt,
                        value: bv,
                    }),
                ) if (aw, au, ab, at) == (bw, bu, bb, bt) => {
                    if !self.machine(av, bv) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}
