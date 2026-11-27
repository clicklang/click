//! Borrow exact pointer payloads and written addresses during certification.
use super::*;
use crate::kernel::{
    Address, AddressBase, AddressOffset, KernelAddressOffset, OffsetTree, OffsetView, Pointer,
    RetainedPointerMetadata, SharedAddress, SharedAddressOffset, SharedPointer,
};
use std::borrow::Cow;

#[derive(Clone, Copy)]
enum BorrowedAddress<'a> {
    Native(&'a Address),
    Shared(&'a SharedAddress),
}
impl<'a> BorrowedAddress<'a> {
    fn parts(self) -> (&'a AddressBase, Offset<'a>) {
        match self {
            Self::Native(value) => (&value.base, Offset::Native(&value.offset)),
            Self::Shared(value) => (value.atom(), Offset::Shared(value.offset())),
        }
    }
}

#[derive(Clone, Copy)]
enum Offset<'a> {
    Native(&'a AddressOffset),
    Shared(&'a SharedAddressOffset),
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
        value: ScaledIndex<'a>,
    },
}
/// A scaled offset's index: a native offset's view owns its retained index;
/// a shared offset's index operand borrows from the offset.
enum ScaledIndex<'a> {
    Native(crate::kernel::SharedMachineIntegerTerm),
    Shared(Operand<'a>),
}
impl ScaledIndex<'_> {
    fn operand(&self) -> Operand<'_> {
        match self {
            Self::Native(index) => index.operand_view(),
            Self::Shared(operand) => *operand,
        }
    }
}
impl<'a> Offset<'a> {
    fn node(self) -> Option<OffsetNode<'a>> {
        use KernelAddressOffset as K;
        use OffsetNode as V;
        let shared_index = |value: &'a KernelTerm| {
            let KernelType::Program(ty) = value.ty() else {
                return None;
            };
            let ty = MachineIntegerType::from_program_type(*ty)?;
            // The native offset exporter preserves opaque index payloads as
            // native operands. Do not grant them shared-root identity here.
            let operand = if let Some(native) = value.retained_machine_input() {
                Operand::Old(native)
            } else {
                Operand::Shared(value)
            };
            Some((ty, operand))
        };
        Some(match self {
            Self::Native(offset) => match offset.view() {
                OffsetView::Constant(value) => V::Constant(value),
                OffsetView::Variable(value) => V::Variable(value),
                OffsetView::Add(a, b) => V::Add([Self::Native(a), Self::Native(b)]),
                OffsetView::Int32Scaled { index, byte_width } => V::Scaled {
                    wide: false,
                    unsigned: false,
                    byte_width,
                    ty: index.ty(),
                    value: ScaledIndex::Native(index),
                },
                OffsetView::Int64Scaled {
                    index,
                    byte_width,
                    unsigned,
                } => V::Scaled {
                    wide: true,
                    unsigned,
                    byte_width,
                    ty: index.ty(),
                    value: ScaledIndex::Native(index),
                },
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
                        value: ScaledIndex::Shared(value),
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
                        value: ScaledIndex::Shared(value),
                    }
                }
            },
        })
    }
}

#[derive(Clone, Copy)]
enum Value<'a> {
    Native(&'a Pointer),
    Shared(&'a SharedPointer),
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
    fn address(self) -> BorrowedAddress<'a> {
        match self {
            Self::Native(value) => BorrowedAddress::Native(value.address()),
            Self::Shared(value) => BorrowedAddress::Shared(&value.node().address),
        }
    }
    fn provenance(self) -> BorrowedAddress<'a> {
        match self {
            Self::Native(value) => BorrowedAddress::Native(value.provenance()),
            Self::Shared(value) => BorrowedAddress::Shared(&value.node().provenance),
        }
    }
    fn bounds_owner(self) -> Option<BorrowedAddress<'a>> {
        match self {
            Self::Native(value) => value.bounds_owner().map(BorrowedAddress::Native),
            Self::Shared(value) => value.node().array.owner().map(BorrowedAddress::Shared),
        }
    }
    fn count(self) -> Option<Operand<'a>> {
        match self {
            Self::Native(value) => value.len().map(Operand::Old),
            Self::Shared(value) => value.len().map(Operand::Shared),
        }
    }
    fn bounds(self) -> Option<(BorrowedAddress<'a>, Operand<'a>)> {
        match self {
            Self::Native(value) => value.bounds().map(|bounds| {
                (
                    BorrowedAddress::Native(&bounds.start()),
                    Operand::Old(&bounds.width()),
                )
            }),
            Self::Shared(value) => value.node().array.bounds().map(|bounds| {
                (
                    BorrowedAddress::Shared(&bounds.start),
                    Operand::Shared(&bounds.width()),
                )
            }),
        }
    }
}

struct Array<'a> {
    memory: crate::kernel::program_point::ReadKey,
    element_type: ProgramType,
    pointer: Value<'a>,
}
impl<'a> Array<'a> {
    fn argument(argument: CallArgument<'a>) -> Option<Self> {
        match argument {
            CallArgument::Native(A::ArrayRef {
                point,
                pointer: ProgramValue::Pointer(pointer),
                element_type,
            }) => Some(Self {
                memory: point.read_key(),
                element_type: *element_type,
                pointer: Value::Native(pointer),
            }),
            CallArgument::Shared(root) => {
                let N::ArrayReference {
                    point,
                    pointer,
                    element_type,
                } = root.node()
                else {
                    return None;
                };
                Some(Self {
                    memory: point.read_key(),
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
    pub(super) fn pointer(&mut self, a: &Address, b: &Address) -> bool {
        self.addresses(BorrowedAddress::Native(a), BorrowedAddress::Native(b))
    }
    pub(super) fn shared_addresses(&mut self, a: &SharedAddress, b: &SharedAddress) -> bool {
        self.addresses(BorrowedAddress::Shared(a), BorrowedAddress::Shared(b))
    }
    pub(super) fn pointer_value(&mut self, a: &Pointer, b: &Pointer) -> bool {
        self.pointer_values(Value::Native(a), Value::Native(b))
    }
    fn pointer_values(&mut self, a: Value<'_>, b: Value<'_>) -> bool {
        if a.metadata() != b.metadata()
            || !self.addresses(a.address(), b.address())
            || !self.addresses(a.provenance(), b.provenance())
        {
            return false;
        }
        match (a.bounds_owner(), b.bounds_owner()) {
            (Some(a), Some(b)) if self.addresses(a, b) => {}
            (None, None) => {}
            _ => return false,
        }
        // A wide pointer's element count is compared as written syntax, as
        // any machine operand is.
        match (a.count(), b.count()) {
            (Some(a), Some(b)) if self.machine(a, b) => {}
            (None, None) => {}
            _ => return false,
        }
        match (a.bounds(), b.bounds()) {
            (Some((ap, aw)), Some((bp, bw))) => {
                if !self.addresses(ap, bp) {
                    return false;
                }
                // Bounds widths have an existing native-syntax admission rule.
                // Export only this selected width, never the complete pointer;
                // a shared identity shortcut would admit additional widths.
                let native = |value| match value {
                    Operand::Old(value) => Cow::Borrowed(value),
                    Operand::Shared(root) => Cow::Owned(
                        crate::kernel::KernelTermExport::machine(root).expect("bounds width"),
                    ),
                };
                let (aw, bw) = (native(aw), native(bw));
                self.machine(Operand::Old(&aw), Operand::Old(&bw))
            }
            (None, None) => true,
            _ => false,
        }
    }
    fn addresses(&mut self, a: BorrowedAddress<'_>, b: BorrowedAddress<'_>) -> bool {
        use OffsetNode as O;
        let ((ab, ao), (bb, bo)) = (a.parts(), b.parts());
        let blocks = match (ab, bb) {
            (AddressBase::PureFunctionApplication(a), AddressBase::PureFunctionApplication(b)) => {
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
                    if !self.machine(av.operand(), bv.operand()) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}
