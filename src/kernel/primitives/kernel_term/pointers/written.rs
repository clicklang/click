//! [`Pointer`]: the production pointer, the written view of a kernel
//! [`SharedPointer`] handle.
//!
//! A kernel pointer's equality is exact producer identity: the handle
//! itself. Pointer-keyed maps, facts and fact-set priorities instead compare
//! pointers logically, by their address, provenance and array object, and
//! ignore the type and the qualifiers. [`Pointer`] is that view of the same
//! handle. Its equality, order and hash are those of the native pointer
//! struct it replaced, with the same hash stream.
//!
//! A handle is written when every address it holds is a written address
//! ([`SharedAddress::written`]) and its bounds width has its written machine
//! term. Every [`Pointer`] is written: one is built from written parts, or
//! from a kernel handle by [`SharedPointer::export`], which checks. A kernel
//! rewrite can build a handle that is not written; it is read through the
//! kernel payload only.
use super::*;
use std::cmp::Ordering;
use std::sync::OnceLock;

/// A machine-integer component of a pointer, such as a bounds width or a
/// wide pointer's element count: the kernel term the kernel reads and the
/// written machine term the written view reads. At least one is set; the
/// other is built from it when first read, by the import or export that used
/// to run when the pointer crossed between the two representations.
#[derive(Clone)]
pub(crate) struct MachineComponent {
    format: MachineIntegerType,
    kernel: OnceLock<KernelTerm>,
    written: OnceLock<Result<OldMachineTerm, &'static str>>,
}

impl MachineComponent {
    pub(in crate::kernel::primitives::kernel_term) fn kernel(
        format: MachineIntegerType,
        term: KernelTerm,
    ) -> Self {
        Self {
            format,
            kernel: OnceLock::from(term),
            written: OnceLock::new(),
        }
    }

    fn written(format: MachineIntegerType, term: OldMachineTerm) -> Self {
        Self {
            format,
            kernel: OnceLock::new(),
            written: OnceLock::from(Ok(term)),
        }
    }

    pub(in crate::kernel::primitives::kernel_term) fn kernel_term(&self) -> &KernelTerm {
        self.kernel.get_or_init(|| {
            let Some(Ok(written)) = self.written.get() else {
                unreachable!("a pointer component has a kernel or a written term")
            };
            KernelTerm::retained_machine_operand(self.format, MachineOperandView::Old(written))
        })
    }

    pub(in crate::kernel::primitives::kernel_term) fn try_written(
        &self,
    ) -> Result<&OldMachineTerm, &'static str> {
        self.written
            .get_or_init(|| {
                KernelTermExport::machine(
                    self.kernel.get().expect("a pointer component has a term"),
                )
            })
            .as_ref()
            .map_err(|error| *error)
    }

    /// The written term of a written handle's component.
    fn written_term(&self) -> &OldMachineTerm {
        match self.written.get() {
            Some(Ok(term)) => term,
            _ => unreachable!("a written pointer's components are written"),
        }
    }
}

impl std::fmt::Debug for MachineComponent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.written.get(), self.kernel.get()) {
            (Some(Ok(width)), _) => width.fmt(f),
            (_, Some(width)) => width.fmt(f),
            _ => f.write_str("<component>"),
        }
    }
}

// SAFETY (for every cast below): `Address`, `ArrayObject`, `SubobjectBounds`
// and `Pointer` are `repr(transparent)` wrappers of `SharedAddress`,
// `KernelArrayObject`, `KernelSubobjectBounds` and `SharedPointer`, and the
// casts are only applied to parts of a written handle.
fn address_view(address: &SharedAddress) -> &Address {
    address.written_view()
}

/// The subobject a pointer was formed from, narrower than its complete
/// object (`design/pointer-subobject-bounds.md`): the written view of a
/// kernel pointer's bounds. C11 6.5.6p7-p8 and C++ [expr.add] bound pointer
/// arithmetic and access by the designated object, not by the enclosing
/// allocation: `&pair.first + 1` is one past `first`, even though
/// `pair.second` lives at that address.
///
/// The bounds are absolute, `[start, start + width)` bytes, so they do not
/// change as the pointer moves through arithmetic or loops. Respelling the
/// pointer's address through a proven alias leaves them alone; a
/// substitution of the variables the address mentions maps `start` the same
/// way. A value without concrete bounds either has a known complete object or
/// carries an opaque domain whose bounds come from coverage evidence.
///
/// The term-valued width also supports the legacy symbolic-bounds prototype.
/// Production unseen pointers use `Pointer::bounds_owner` instead
/// (`design/pointer-subobject-bounds.md`, Phase C).
///
/// Equality, order and hash are the native struct's derived ones: the
/// start, then the width.
#[repr(transparent)]
#[derive(Clone)]
pub struct SubobjectBounds(KernelSubobjectBounds);

impl SubobjectBounds {
    pub(crate) fn new(start: Address, width: OldMachineTerm) -> Self {
        Self(KernelSubobjectBounds {
            start: start.into_shared(),
            width: MachineComponent::written(MachineIntegerType::Int32, width),
        })
    }

    fn from_kernel(bounds: &KernelSubobjectBounds) -> &Self {
        // SAFETY: see the note above `address_view`.
        unsafe { &*(bounds as *const KernelSubobjectBounds as *const Self) }
    }

    pub(crate) fn start(&self) -> &Address {
        address_view(&self.0.start)
    }

    pub(crate) fn width(&self) -> &OldMachineTerm {
        self.0.width.written_term()
    }

    fn key(&self) -> (&Address, &OldMachineTerm) {
        (self.start(), self.width())
    }
}

impl std::fmt::Debug for SubobjectBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SubobjectBounds")
            .field("start", self.start())
            .field("width", self.width())
            .finish()
    }
}
impl PartialEq for SubobjectBounds {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}
impl Eq for SubobjectBounds {}
impl PartialOrd for SubobjectBounds {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SubobjectBounds {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(&other.key())
    }
}
impl Hash for SubobjectBounds {
    /// The native struct's derived stream: start, then width.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.start().hash(state);
        self.width().hash(state);
    }
}

/// The C array object a pointer was derived from (C11 6.5.6p8-9): the part of
/// its C provenance below the allocation, read through a written pointer's
/// kernel array object. Arithmetic, one-past pointers, subtraction and
/// accesses are bounded by it, not by the allocation.
///
/// The kernel object is one of: the complete object the provenance names
/// (a local, a global, a heap block, a temporary or a function); an opaque
/// array object whose creation the kernel did not see, as for a parameter or
/// a loaded pointer, named by where the pointer came from (coverage facts
/// about that name give its extent; a view that may not use the name's
/// coverage has no name); or a member subobject of the allocation, with its
/// bytes (a memory range's carrier has none of its own: the range's bytes
/// are its bounds) and the opaque array object it was selected from.
#[repr(transparent)]
#[derive(Clone)]
pub(in crate::kernel) struct ArrayObject(KernelArrayObject);

/// The native enum's shape, for its derived equality, order and hash.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ArrayObjectKey<'a> {
    Allocation,
    Opaque(Option<&'a Address>),
    Member(MemberArrayKey<'a>),
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
struct MemberArrayKey<'a> {
    bounds: Option<&'a SubobjectBounds>,
    within: Option<&'a Address>,
}

impl ArrayObject {
    fn from_kernel(array: &KernelArrayObject) -> &Self {
        // SAFETY: see the note above `address_view`.
        unsafe { &*(array as *const KernelArrayObject as *const Self) }
    }

    pub(in crate::kernel) fn allocation() -> Self {
        Self(KernelArrayObject::Allocation)
    }

    pub(in crate::kernel) fn opaque(owner: Option<Address>) -> Self {
        Self(KernelArrayObject::Opaque(owner.map(Address::into_shared)))
    }

    /// The array object with these bounds and opaque name, as the three
    /// separate fields spelled it: `known` is false only for an opaque array
    /// object, which has no bounds of its own.
    pub(in crate::kernel) fn from_parts(
        known: bool,
        bounds: Option<SubobjectBounds>,
        owner: Option<Address>,
    ) -> Self {
        Self(KernelArrayObject::from_parts(
            known,
            bounds.map(|bounds| bounds.0),
            owner.map(Address::into_shared),
        ))
    }

    pub(in crate::kernel) fn is_known(&self) -> bool {
        self.0.is_known()
    }

    /// Whether this is the complete object the provenance names.
    pub(in crate::kernel) fn is_allocation(&self) -> bool {
        matches!(self.0, KernelArrayObject::Allocation)
    }

    pub(in crate::kernel) fn bounds(&self) -> Option<&SubobjectBounds> {
        self.0.bounds().map(SubobjectBounds::from_kernel)
    }

    /// The opaque array object this one is or was selected from.
    pub(in crate::kernel) fn owner(&self) -> Option<&Address> {
        self.0.owner().map(address_view)
    }

    /// The name of an opaque array object.
    pub(in crate::kernel) fn opaque_owner(&self) -> Option<&Address> {
        self.0.opaque_owner().map(address_view)
    }

    pub(in crate::kernel) fn with_bounds(&self, bounds: Option<SubobjectBounds>) -> Self {
        if bounds.is_none() && self.bounds().is_none() {
            return self.clone();
        }
        Self::from_parts(true, bounds, self.owner().cloned())
    }

    pub(in crate::kernel) fn with_owner(&self, owner: Option<Address>) -> Self {
        Self::from_parts(self.is_known(), self.bounds().cloned(), owner)
    }

    pub(in crate::kernel) fn map(&self, mut map: impl FnMut(&Address) -> Address) -> Self {
        self.try_map(|address| Some(map(address)))
            .expect("total address map")
    }

    pub(in crate::kernel) fn try_map(
        &self,
        mut map: impl FnMut(&Address) -> Option<Address>,
    ) -> Option<Self> {
        let mut address = |address: &SharedAddress| map(address_view(address));
        Some(Self(match &self.0 {
            KernelArrayObject::Allocation => KernelArrayObject::Allocation,
            KernelArrayObject::Opaque(owner) => KernelArrayObject::Opaque(match owner {
                Some(owner) => Some(address(owner)?.into_shared()),
                None => None,
            }),
            KernelArrayObject::Member(member) => {
                KernelArrayObject::Member(Arc::new(KernelMemberArray {
                    bounds: match &member.bounds {
                        Some(bounds) => Some(KernelSubobjectBounds {
                            start: address(&bounds.start)?.into_shared(),
                            width: bounds.width.clone(),
                        }),
                        None => None,
                    },
                    within: match &member.within {
                        Some(owner) => Some(address(owner)?.into_shared()),
                        None => None,
                    },
                }))
            }
        }))
    }

    fn key(&self) -> ArrayObjectKey<'_> {
        match &self.0 {
            KernelArrayObject::Allocation => ArrayObjectKey::Allocation,
            KernelArrayObject::Opaque(owner) => {
                ArrayObjectKey::Opaque(owner.as_ref().map(address_view))
            }
            KernelArrayObject::Member(member) => ArrayObjectKey::Member(MemberArrayKey {
                bounds: member.bounds.as_ref().map(SubobjectBounds::from_kernel),
                within: member.within.as_ref().map(address_view),
            }),
        }
    }
}

impl std::fmt::Debug for ArrayObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            KernelArrayObject::Allocation => f.write_str("Allocation"),
            KernelArrayObject::Opaque(_) => {
                f.debug_tuple("Opaque").field(&self.opaque_owner()).finish()
            }
            KernelArrayObject::Member(member) => f
                .debug_struct("Member")
                .field("bounds", &self.bounds())
                .field("within", &member.within.as_ref().map(address_view))
                .finish(),
        }
    }
}
impl PartialEq for ArrayObject {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key()
    }
}
impl Eq for ArrayObject {}
impl PartialOrd for ArrayObject {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for ArrayObject {
    fn cmp(&self, other: &Self) -> Ordering {
        self.key().cmp(&other.key())
    }
}
impl Hash for ArrayObject {
    /// The native enum's derived stream.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key().hash(state);
    }
}

/// The written view of a wide pointer's metadata, as identity compares it
/// (`design/rust-slice-values.md`). A thin pointer has none.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum PointerMetadata<'a> {
    /// A slice's element count, a `UInt64` (`usize`) term.
    ElementCount(&'a OldMachineTerm),
}

impl<'a> PointerMetadata<'a> {
    fn from_kernel(metadata: &'a KernelPointerMetadata) -> Self {
        match metadata {
            KernelPointerMetadata::ElementCount(count) => Self::ElementCount(count.written_term()),
        }
    }

    pub(crate) fn element_count(self) -> &'a OldMachineTerm {
        match self {
            Self::ElementCount(count) => count,
        }
    }
}

/// Hashes nothing for a thin pointer, so a thin pointer's stream is the one
/// it had before metadata existed: fact-set treap priorities are content
/// hashes. Present metadata follows a marker no identity tuple writes in
/// that position, then its own derived stream.
fn hash_pointer_metadata<H: Hasher>(metadata: Option<PointerMetadata<'_>>, state: &mut H) {
    if let Some(metadata) = metadata {
        state.write_u64(WIDE_POINTER_HASH_MARKER);
        metadata.hash(state);
    }
}
const WIDE_POINTER_HASH_MARKER: u64 = 0x7769_6465_2d70_7472; // "wide-ptr"

/// The slice pointer type a thin pointer of type `thin` widens to: `T *`
/// to a pointer to `[T]`. A type that is no slice's thin part is an internal
/// error: the front end builds a slice from a typed element pointer.
pub(super) fn widened_type(thin: ProgramType) -> ProgramType {
    match SliceElement::of_thin_pointer_type(thin) {
        Some(element) => ProgramType::SlicePointer(element),
        None => panic!("internal error: a `{thin:?}` pointer is no slice's thin part"),
    }
}

/// The type of a wide pointer's thin part.
pub(super) fn thin_part_type(wide: ProgramType) -> ProgramType {
    match wide {
        ProgramType::SlicePointer(element) => element.thin_pointer_type(),
        other => panic!("internal error: a wide pointer has the thin type `{other:?}`"),
    }
}

/// A thin pointer is never built at a slice pointer type: every value of
/// that type carries its element count.
#[track_caller]
fn assert_thin_pointer_type(program_type: ProgramType) {
    assert!(
        !program_type.is_slice_pointer(),
        "internal error: a slice pointer is built with its element count \
         (`Pointer::with_element_count`), not as a thin pointer"
    );
}

/// A retyping keeps the value, so it keeps a wide pointer's metadata: a thin
/// pointer retypes only to thin types, a wide one only to slice pointer
/// types, as Rust's `as` between `*const [T]` and `*const [U]` keeps the
/// count. Adding or removing the count is a construction or a projection,
/// never a cast (`design/rust-slice-values.md`, "Representation").
#[track_caller]
pub(super) fn check_retyping(from: ProgramType, to: ProgramType) {
    assert_eq!(
        from.is_slice_pointer(),
        to.is_slice_pointer(),
        "internal error: retyping `{from:?}` to `{to:?}` would add or remove a slice's \
         element count; build it with `with_element_count` or take `as_ptr`"
    );
}

/// A pointer value: an address and its provenance (`design/pointer-model.md`),
/// the written view of a kernel pointer handle (module documentation).
/// C provenance is the allocation the pointer was derived from plus the array
/// object within it (C11 6.5.6p8-9). The term's type is carried beside the
/// value and is not part of its identity: equality, ordering and hashing
/// ignore it, as they ignore the declared object class and type evidence.
///
/// The provenance is the allocation designated when this value entered.
/// Address aliases never replace it; only value transport or substitution
/// maps it. The qualifiers hold the class of the object the pointer was
/// formed to designate, from the declaration that produced it
/// (`design/effective-types.md`): it survives casts, `void *`, arithmetic and
/// copies, so an access through any later spelling is checked against it.
///
/// Building or changing a pointer charges nothing, as the native struct's
/// construction charged nothing. A change builds a new handle unless this
/// value is its only holder.
#[repr(transparent)]
#[derive(Clone)]
pub struct Pointer(SharedPointer);

impl Pointer {
    pub(in crate::kernel) fn from_parts(
        address: Address,
        provenance: Address,
        array: ArrayObject,
        program_type: ProgramType,
    ) -> Self {
        assert_thin_pointer_type(program_type);
        Self(SharedPointer(Arc::new(KernelPointer {
            address: address.into_shared(),
            provenance: provenance.into_shared(),
            array: array.0,
            program_type,
            qualifiers: None,
            metadata: None,
        })))
    }

    /// The kernel handle: the same allocation, compared exactly.
    pub(crate) fn shared(&self) -> &SharedPointer {
        &self.0
    }

    pub(crate) fn into_shared(self) -> SharedPointer {
        self.0
    }

    fn node(&self) -> &KernelPointer {
        &self.0.0
    }

    fn update(&mut self, change: impl FnOnce(&mut KernelPointer)) {
        change(Arc::make_mut(&mut self.0.0));
    }

    pub(crate) fn address(&self) -> &Address {
        address_view(&self.node().address)
    }

    pub(crate) fn provenance(&self) -> &Address {
        address_view(&self.node().provenance)
    }

    /// The array object within the allocation.
    pub(in crate::kernel) fn array_object(&self) -> &ArrayObject {
        ArrayObject::from_kernel(&self.node().array)
    }

    pub(crate) fn program_type(&self) -> ProgramType {
        self.node().program_type
    }

    pub(in crate::kernel) fn qualifiers(&self) -> Option<&KernelPointerQualifiers> {
        self.node().qualifiers.as_deref()
    }

    /// The qualifiers to change, created empty when absent.
    pub(in crate::kernel) fn qualifiers_mut(&mut self) -> &mut KernelPointerQualifiers {
        let value = Arc::make_mut(&mut self.0.0);
        Arc::make_mut(value.qualifiers.get_or_insert_with(Default::default))
    }

    pub(in crate::kernel) fn with_array_object(mut self, array: ArrayObject) -> Self {
        self.update(|value| value.array = array.0);
        self
    }

    pub(in crate::kernel) fn with_provenance(mut self, provenance: Address) -> Self {
        self.update(|value| value.provenance = provenance.into_shared());
        self
    }

    /// The same value at another type. Retyping never adds or removes a
    /// wide pointer's metadata: a thin pointer takes a thin type and a wide
    /// one a slice pointer type ([`check_retyping`]). Widening is
    /// [`Self::with_element_count`] and narrowing [`Self::as_ptr`].
    pub(crate) fn with_type(mut self, program_type: ProgramType) -> Self {
        if self.program_type() != program_type {
            check_retyping(self.program_type(), program_type);
            self.update(|value| value.program_type = program_type);
        }
        self
    }

    /// Respells the address as a proven-equal alias. The bounds keep their
    /// own spelling: it names the same bytes either way, and the access
    /// check resolves the address against it as it resolves a held range.
    pub(crate) fn replace_pointer(&mut self, pointer: Address) {
        self.update(|value| value.address = pointer.into_shared());
    }

    /// The same value at another address in the same subobject: the result
    /// of pointer arithmetic, which keeps the type, qualifiers and bounds.
    pub(crate) fn with_address(mut self, pointer: Address) -> Self {
        self.replace_pointer(pointer);
        self
    }

    pub(crate) fn into_pointer(self) -> Address {
        self.address().clone()
    }

    /// A wide pointer's metadata, read from the value: O(1), no facts.
    pub(crate) fn metadata(&self) -> Option<PointerMetadata<'_>> {
        self.node()
            .metadata
            .as_deref()
            .map(PointerMetadata::from_kernel)
    }

    /// A wide pointer's element count (`s.len()`). `None` for a thin pointer.
    pub(crate) fn len(&self) -> Option<&OldMachineTerm> {
        self.metadata().map(PointerMetadata::element_count)
    }

    pub(crate) fn is_wide(&self) -> bool {
        self.node().metadata.is_some()
    }

    /// The wide pointer with this thin part and element count, a `UInt64`
    /// term (`design/rust-slice-values.md`, "Construction"). Its type is the
    /// slice pointer type whose thin part has this pointer's type
    /// ([`widened_type`]): a `T *` becomes a pointer to `[T]`.
    pub(crate) fn with_element_count(mut self, count: OldMachineTerm) -> Self {
        assert!(
            !self.is_wide(),
            "internal error: a wide pointer is built from a thin pointer"
        );
        let program_type = widened_type(self.program_type());
        self.update(|value| {
            value.program_type = program_type;
            value.metadata = Some(Arc::new(KernelPointerMetadata::ElementCount(
                MachineComponent::written(MachineIntegerType::UInt64, count),
            )))
        });
        self
    }

    /// The same wide pointer with another element count, as a substitution
    /// maps it: the type, `[T]` or `str`, is kept.
    pub(crate) fn with_replaced_element_count(mut self, count: OldMachineTerm) -> Self {
        assert!(
            self.is_wide(),
            "internal error: only a wide pointer has an element count to replace"
        );
        self.update(|value| {
            value.metadata = Some(Arc::new(KernelPointerMetadata::ElementCount(
                MachineComponent::written(MachineIntegerType::UInt64, count),
            )))
        });
        self
    }

    /// The thin part (`s.as_ptr()`): the same address, provenance and array
    /// object, with no metadata, at the element's thin pointer type. A thin
    /// pointer is its own thin part.
    pub(crate) fn as_ptr(&self) -> Self {
        let mut thin = self.clone();
        if thin.is_wide() {
            let program_type = thin_part_type(thin.program_type());
            thin.update(|value| {
                value.program_type = program_type;
                value.metadata = None;
            });
        }
        thin
    }

    /// Whether the two carry the same metadata as identity compares it. Two
    /// thin pointers do.
    pub(crate) fn same_metadata_as(&self, other: &Self) -> bool {
        self.metadata() == other.metadata()
    }

    /// Refuse a wide pointer where an operation reads only a thin one and has
    /// no form for its metadata yet. This is an internal error, never a
    /// fallback that drops the length (`design/rust-slice-values.md`, steps
    /// 2b-ii and 2b-iii).
    #[track_caller]
    pub(crate) fn expect_thin(&self, operation: &str) -> &Self {
        if self.is_wide() {
            panic!(
                "internal error: {operation} has no form for a wide pointer's metadata yet \
                 (design/rust-slice-values.md, steps 2b-ii and 2b-iii)"
            );
        }
        self
    }

    /// Everything that is a thin value's identity: the address, its provenance,
    /// and the subobject it designates, plus its opaque local-reference
    /// custody. A lease key is a fresh scalar id, never a structural resource
    /// or ledger key. Two values at one address with different bounds are
    /// different values: address equality does not make a one-past pointer
    /// designate the object that follows it. A wide pointer's identity adds
    /// its metadata ([`Self::metadata`]), compared after this tuple.
    #[allow(clippy::type_complexity)]
    fn identity(
        &self,
    ) -> (
        &Address,
        &Address,
        bool,
        Option<&Address>,
        Option<&SubobjectBounds>,
    ) {
        let array = self.array_object();
        (
            self.address(),
            self.provenance(),
            array.is_known(),
            array.opaque_owner(),
            array.bounds(),
        )
    }

    /// Whether the two have one C provenance, as identity compares it: the
    /// same allocation and the same array object.
    pub(crate) fn same_provenance_as(&self, other: &Self) -> bool {
        let (_, provenance, known, owner, bounds) = self.identity();
        let (_, other_provenance, other_known, other_owner, other_bounds) = other.identity();
        provenance == other_provenance
            && known == other_known
            && owner == other_owner
            && bounds == other_bounds
    }
}

impl std::fmt::Debug for Pointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug = f.debug_struct("Pointer");
        debug
            .field("address", self.address())
            .field("provenance", self.provenance())
            .field("array", self.array_object())
            .field("program_type", &self.program_type())
            .field("qualifiers", &self.qualifiers());
        // A thin pointer prints as it did before metadata existed.
        if let Some(metadata) = self.metadata() {
            debug.field("metadata", &metadata);
        }
        debug.finish()
    }
}
impl PartialEq for Pointer {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
            || (self.identity() == other.identity() && self.metadata() == other.metadata())
    }
}
impl Eq for Pointer {}
impl PartialOrd for Pointer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Pointer {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0 == other.0 {
            return Ordering::Equal;
        }
        // Thin pointers order as before; a thin pointer precedes a wide one
        // with the same thin part.
        self.identity()
            .cmp(&other.identity())
            .then_with(|| self.metadata().cmp(&other.metadata()))
    }
}
impl Hash for Pointer {
    /// The native struct's identity stream. Fact-set treap priorities hash
    /// pointers, so the values are kept; metadata adds to the stream only
    /// when present ([`hash_pointer_metadata`]).
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
        hash_pointer_metadata(self.metadata(), state);
    }
}
impl std::ops::Deref for Pointer {
    type Target = Address;
    fn deref(&self) -> &Address {
        self.address()
    }
}

impl SharedPointer {
    /// The written view of this handle, or why one of its parts has no
    /// written form. A handle whose parts are written is shared, not copied;
    /// otherwise an address whose block has an observation key's identity
    /// is given a written address's identity ([`SharedAddress::export`]).
    pub(crate) fn export(&self) -> Result<Pointer, &'static str> {
        let value = self.node();
        let mut same = true;
        let mut address = |address: &SharedAddress| -> Result<SharedAddress, &'static str> {
            let written = address.export()?.into_shared();
            same &= written.same_handle(address);
            Ok(written)
        };
        let pointer = address(&value.address)?;
        let provenance = address(&value.provenance)?;
        let array = match &value.array {
            KernelArrayObject::Allocation => KernelArrayObject::Allocation,
            KernelArrayObject::Opaque(owner) => {
                KernelArrayObject::Opaque(owner.as_ref().map(&mut address).transpose()?)
            }
            KernelArrayObject::Member(member) => {
                let bounds = match &member.bounds {
                    Some(bounds) => {
                        let start = address(&bounds.start)?;
                        bounds.width.try_written()?;
                        Some(KernelSubobjectBounds {
                            start,
                            width: bounds.width.clone(),
                        })
                    }
                    None => None,
                };
                let within = member.within.as_ref().map(&mut address).transpose()?;
                KernelArrayObject::Member(Arc::new(KernelMemberArray { bounds, within }))
            }
        };
        if let Some(metadata) = &value.metadata {
            match metadata.as_ref() {
                KernelPointerMetadata::ElementCount(count) => {
                    count.try_written()?;
                }
            }
        }
        if same {
            return Ok(Pointer(self.clone()));
        }
        Ok(Pointer(SharedPointer(Arc::new(KernelPointer {
            address: pointer,
            provenance,
            array,
            program_type: value.program_type,
            qualifiers: value.qualifiers.clone(),
            metadata: value.metadata.clone(),
        }))))
    }
}
