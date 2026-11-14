//! Contract-facing declarations shared by the C, C++ and Rust frontends.
//!
//! Source compatibility metadata is retained here. C source bodies and their
//! parsing/lowering extensions remain in the C frontend.

use super::c::syntax::CAbi;
use super::c::syntax::{
    C0EnumDefinition, C0Expression, C0Global, C0GlobalAggregate, C0GlobalAggregateArray,
    C0GlobalArray, C0Statement, C0StaticAggregate, C0StaticAggregateArray, C0StaticArray,
    C0StaticLocal, C0StringLiteral, C0UnionLayout, DeclarationMap,
};
use super::c::target::{LongRank, PlainChar};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportedFunction {
    pub(crate) program_entry_state: Option<std::sync::Arc<crate::kernel::ExecutionState>>,
    /// A typed language frontend may provide executable kernel semantics
    /// directly while reusing this declaration interface for Surface Click
    /// contract checking. C parsing always leaves this absent.
    pub(super) prelowered_kernel_function: Option<crate::kernel::ProgramFunction>,
    pub(super) return_type: InterfaceType,
    pub(super) return_pointee_constant: bool,
    pub(super) return_reference: bool,
    pub(super) return_struct_name: Option<String>,
    /// A foreign opaque declaration can retain result construction without
    /// carrying an executable body. Ordinary C aggregate results use Copy.
    pub(super) aggregate_return_mode: crate::kernel::AggregateReturnMode,
    pub(super) return_pointer_struct_name: Option<String>,
    /// The C spelling used by a sidecar contract. Header-provided internal
    /// functions use a translation-unit-qualified kernel name in `name`.
    pub(super) source_name: String,
    pub(super) name: String,
    pub(super) inline_body: bool,
    /// Calls used as expression observers must have contracts with views only.
    pub(super) requires_read_only_contract: bool,
    /// The declaration names its parameters only by position, as a Rust
    /// `extern` block item does in Charon's output; the sidecar head names
    /// them ([`Self::named_by_head`]).
    pub(super) positional_parameters: bool,
    /// A closure's leading parameters that are the variables it captures. A
    /// sidecar names only the closure's own parameters; its contract reads
    /// the captures by name.
    pub(super) closure_captures: usize,
    /// The interface function a crate trait method's implementation
    /// implements, whose contract its own must refine.
    pub(super) trait_interface: Option<String>,
    /// The generic function this declaration is an instance of, verified
    /// once for every type; the instance's contract is its contract at the
    /// declaration's types.
    pub(super) generic_instance: Option<String>,
    /// The C++ virtual method a dispatch the importer names stands for.
    pub(super) dispatched_method: Option<String>,
    /// A C++ function's calls of methods on a receiver that may be an object
    /// of a derived class: the function called, and the reference parameter
    /// the receiver is, or `None` for `this`.
    pub(super) receiver_calls: Vec<(String, Option<String>)>,
    pub(super) parameters: Vec<ImportedParameter>,
    pub(super) body: C0Statement,
    /// Compiler-created carriers for statement-form callback calls. Keeping
    /// their origins explicit distinguishes them from user declarations with
    /// similar names and lets diagnostics name the written callback pointer.
    pub(super) callback_statement_sources: std::sync::Arc<BTreeMap<String, C0Expression>>,
    /// Function-scope C label spellings resolved to kernel identities and
    /// executable statement indices after the complete body is parsed.
    pub(super) control_targets: BTreeMap<String, (crate::kernel::ControlTargetId, usize)>,
    pub(super) structs: DeclarationMap<RecordLayout>,
    pub(super) enums: DeclarationMap<C0EnumDefinition>,
    pub(super) unions: DeclarationMap<C0UnionLayout>,
    pub(super) globals: DeclarationMap<C0Global>,
    pub(super) global_arrays: DeclarationMap<C0GlobalArray>,
    pub(super) global_aggregates: DeclarationMap<C0GlobalAggregate>,
    pub(super) global_aggregate_arrays: DeclarationMap<C0GlobalAggregateArray>,
    pub(super) static_locals: BTreeMap<String, C0StaticLocal>,
    pub(super) static_arrays: BTreeMap<String, C0StaticArray>,
    pub(super) static_aggregates: BTreeMap<String, C0StaticAggregate>,
    pub(super) static_aggregate_arrays: BTreeMap<String, C0StaticAggregateArray>,
    /// The struct name of each automatic local of struct-pointer type, keyed
    /// by its C spelling. A sidecar names a local by that spelling, so this is
    /// what gives `have p->value == root->value` a layout for `p`; globals,
    /// static locals and aggregates already travel in the maps above. A
    /// spelling declared twice in one function with two struct types is
    /// dropped rather than guessed.
    pub(super) local_struct_pointers: BTreeMap<String, String>,
    /// Struct type of each unambiguous automatic struct value, indexed by
    /// the spelling a Click sidecar uses.
    pub(super) local_struct_values: BTreeMap<String, String>,
    /// The automatic locals of reference type, by the name the source gives
    /// each. Its carrying pointer is the local [`reference_carrier_name`]
    /// names.
    pub(super) local_references: BTreeSet<String>,
    /// The automatic locals of pointer type, by C spelling. A sidecar
    /// comparison doing arithmetic on one keeps its C meaning. A spelling
    /// declared both as a pointer and not is left out.
    pub(super) local_pointers: BTreeSet<String>,
    pub(super) string_literals: Vec<C0StringLiteral>,
    /// For a Rust function, the iterator each loop advances, by loop index
    /// (the loops in preorder): the state a proof names `iter` in that loop
    /// and `loop(i).iter` elsewhere.
    pub(super) loop_iterators: Vec<Option<RustLoopIterator>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportedParameter {
    pub(super) interface_type: InterfaceType,
    pub(super) name: String,
    pub(super) volatile: bool,
    pub(super) pointee_volatile: bool,
    pub(super) constant: bool,
    pub(super) pointee_constant: bool,
    /// Whether the source declares a reference, as C++ `int&` does. The
    /// parameter's type is the pointer that carries it.
    pub(super) reference: bool,
    pub(super) slice_length_parameter: Option<usize>,
    pub(super) fixed_reference_extent: Option<u32>,
    pub(super) struct_name: Option<String>,
    pub(super) union_name: Option<String>,
    pub(super) struct_layout: Option<RecordLayout>,
    /// The layout of the pointee when the parameter is a pointer to a struct,
    /// so `*p` resources can type the object's cells field by field.
    /// Distinct from `struct_layout`, which marks struct values and arrays.
    pub(super) pointee_struct_layout: Option<RecordLayout>,
    pub(super) function_pointer_signature: Option<CallbackInterface>,
    /// The ABI width of one element when the source parameter was declared as
    /// an array of structs. The public C0 type remains the compatible
    /// struct-pointer placeholder, while the kernel uses byte addressing for
    /// the lowered indexed field accesses.
    pub(super) array_element_width: Option<u32>,
    /// The struct a struct-pointer parameter points to, as a strict-aliasing
    /// class (`design/effective-types.md`).
    pub(super) pointee_struct_class: Option<crate::kernel::effective_type::CAccessClass>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum InterfaceType {
    /// Plain char is distinct from both `signed char` and `unsigned char` in
    /// C compatibility. Its signedness is the target's, fixed when the source
    /// is parsed: unsigned for the Linux kernel target, signed for x86-64
    /// user space. Its values and kernel representation are those of
    /// [`PlainChar::byte_type`].
    Char(PlainChar),
    CharPointer(PlainChar),
    CharPointerPointer(PlainChar),
    CharArray(PlainChar, u32),
    /// A value of an abstract type parameter, as in a generic Rust trait's
    /// interface; its kernel type is `ProgramType::Parameter`.
    Parameter(crate::kernel::TypeParameterName),
    /// A pointer to one, a Rust `&T`; its kernel type is
    /// `ProgramType::ParameterPointer`.
    ParameterPointer(crate::kernel::TypeParameterName),
    Void,
    Bool,
    /// An opaque pointer to an object of unknown type. It preserves pointer
    /// identity and provenance but deliberately has no pointee width, so it
    /// cannot be indexed, dereferenced, or used in pointer arithmetic until
    /// an explicit conversion supplies a modeled object type.
    VoidPointer,
    /// Opaque pointer to a `void *` result slot. The declaration model keeps
    /// its exact type without assuming that pthread_join writes through it.
    VoidPointerPointer,
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    /// `long` or `long long` ([`LongRank`]): distinct, incompatible C types
    /// with the same LP64 representation, which [`Self::erase_long_rank`]
    /// gives. The pointer, pointer-pointer and array forms carry the rank of
    /// their element type.
    Int64(LongRank),
    UInt64(LongRank),
    /// Kernel wide scalars; source parsing/admission remains unsupported.
    Int128,
    UInt128,
    Float32,
    Float64,
    Int8Pointer,
    Int16Pointer,
    UInt16Pointer,
    Int32Pointer,
    UInt8Pointer,
    UInt32Pointer,
    Int64Pointer(LongRank),
    Int128Pointer,
    UInt64Pointer(LongRank),
    UInt128Pointer,
    Float32Pointer,
    Float64Pointer,
    Int8PointerPointer,
    Int16PointerPointer,
    UInt16PointerPointer,
    Int32PointerPointer,
    UInt8PointerPointer,
    UInt32PointerPointer,
    Int64PointerPointer(LongRank),
    Int128PointerPointer,
    UInt64PointerPointer(LongRank),
    UInt128PointerPointer,
    Float32PointerPointer,
    Float64PointerPointer,
    /// A callback signature identified by a stable, structural signature key.
    /// The key is shared with the kernel type and is deliberately opaque to
    /// ordinary C expressions: function pointers are callable, not objects.
    FunctionPointer(crate::kernel::CallbackSignature),
    Int32Array(u32),
    UInt8Array(u32),
    Int8Array(u32),
    Int16Array(u32),
    UInt16Array(u32),
    UInt32Array(u32),
    Int64Array(LongRank, u32),
    Int128Array(u32),
    UInt64Array(LongRank, u32),
    UInt128Array(u32),
    Float32Array(u32),
    Float64Array(u32),
    /// An array of pointers. The kernel element erases the `long`/`long
    /// long` rank of a 64-bit integer pointee, which [`LongRank`] keeps (and
    /// is [`LongRank::Long`] for every other element).
    PointerArray(crate::kernel::PointerArrayElement, LongRank, u32),
}

/// The nominal part of a callback signature that the kernel's structural
/// `ProgramType::FunctionPointer` deliberately does not carry.  The ABI signature
/// remains structural; these tags are checked while parsing C0 expressions so
/// `struct left *` and `struct right *` cannot silently become interchangeable
/// callback arguments.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallbackParameter {
    pub(super) interface_type: InterfaceType,
    pub(super) struct_name: Option<String>,
    pub(super) pointee_constant: bool,
}

/// Nominal metadata for a function-pointer type.  `interface_type` and the kernel
/// signature key still describe the ABI shape; `struct_name` retains the C
/// spelling needed for boundary checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallbackInterface {
    pub(super) return_type: InterfaceType,
    pub(super) return_struct_name: Option<String>,
    pub(super) return_pointee_constant: bool,
    pub(super) parameters: Vec<CallbackParameter>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordLayout {
    pub(super) fields: BTreeMap<String, RecordField>,
    /// Leaf fields used when a struct value is copied through the kernel.
    /// Embedded struct fields are flattened here while preserving their
    /// declared names as qualified paths and their complete ABI offsets.
    pub(super) aggregate_fields: Vec<RecordScalarField>,
    /// Address-overlapping union storage retained separately from scalar leaf
    /// fields. Flattening union members into `aggregate_fields` would make a
    /// by-value copy overwrite one member with another.
    pub(super) aggregate_unions: Vec<RecordUnionLayout>,
    pub(super) size_bytes: u32,
    pub(super) alignment_bytes: u32,
    /// The struct's strict-aliasing class (`design/effective-types.md`),
    /// for a struct the C parser declared.
    pub(super) class: Option<crate::kernel::effective_type::CStructClass>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordField {
    pub(super) interface_type: InterfaceType,
    pub(super) long_double: bool,
    pub(super) pointee_constant: bool,
    pub(super) struct_name: Option<String>,
    pub(super) enum_name: Option<String>,
    pub(super) union_name: Option<String>,
    pub(super) function_pointer_signature: Option<CallbackInterface>,
    /// The ABI width of one element when this is an inline array of embedded
    /// structs. The public C0 type remains a byte-array placeholder, while
    /// member selection uses this metadata to preserve struct indexing.
    pub(super) array_element_width: Option<u32>,
    /// The fixed dimensions of a multidimensional inline array, in C's
    /// declared order. The shape is retained so indexing can be flattened
    /// with the correct row-major stride.
    pub(super) array_shape: Option<Vec<u32>>,
    pub(super) offset_bytes: u32,
    pub(super) byte_width: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RecordScalarField {
    pub(super) pointee_constant: bool,
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) interface_type: InterfaceType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RecordUnionField {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) interface_type: InterfaceType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct RecordUnionLayout {
    pub(super) name: String,
    pub(super) offset_bytes: u32,
    pub(super) size_bytes: u32,
    pub(super) fields: Vec<RecordUnionField>,
}

impl CallbackParameter {
    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub(crate) fn new(
        interface_type: InterfaceType,
        struct_name: Option<String>,
        pointee_constant: bool,
    ) -> Self {
        Self {
            interface_type,
            struct_name,
            pointee_constant,
        }
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }
}

impl CallbackInterface {
    pub fn return_pointee_is_constant(&self) -> bool {
        self.return_pointee_constant
    }

    pub(crate) fn new(
        return_type: InterfaceType,
        return_struct_name: Option<String>,
        parameters: Vec<CallbackParameter>,
        return_pointee_constant: bool,
    ) -> Self {
        Self {
            return_type,
            return_struct_name,
            parameters,
            return_pointee_constant,
        }
    }

    pub fn return_type(&self) -> InterfaceType {
        self.return_type
    }

    pub fn return_struct_name(&self) -> Option<&str> {
        self.return_struct_name.as_deref()
    }

    pub fn parameters(&self) -> &[CallbackParameter] {
        &self.parameters
    }

    /// The same signature with every `long long` rank erased to `long`, for
    /// matching against a Click specification type that does not spell it.
    pub fn erase_long_rank(&self) -> Self {
        let mut erased = self.clone();
        erased.return_type = erased.return_type.erase_long_rank();
        for parameter in &mut erased.parameters {
            parameter.interface_type = parameter.interface_type.erase_long_rank();
        }
        erased
    }
}

impl InterfaceType {
    /// The type's name in diagnostics: Click's kernel-style name, without the
    /// `long`/`long long` rank, which Click specification types do not spell.
    pub fn diagnostic_name(self) -> String {
        format!("{self:?}")
            .replace("(LongLong, ", "(")
            .replace("(Long, ", "(")
            .replace("(LongLong)", "")
            .replace("(Long)", "")
    }

    /// The type's name where its `long`/`long long` rank can be what differs:
    /// a 64-bit integer type is spelled in C, any other by
    /// [`Self::diagnostic_name`].
    pub fn ranked_diagnostic_name(self) -> String {
        match self {
            Self::Int64(rank) => rank.signed_spelling().to_string(),
            Self::UInt64(rank) => rank.unsigned_spelling().to_string(),
            Self::Int64Pointer(rank) => format!("{} *", rank.signed_spelling()),
            Self::UInt64Pointer(rank) => format!("{} *", rank.unsigned_spelling()),
            Self::Int64PointerPointer(rank) => format!("{} **", rank.signed_spelling()),
            Self::UInt64PointerPointer(rank) => format!("{} **", rank.unsigned_spelling()),
            other => other.diagnostic_name(),
        }
    }

    pub(crate) fn abi_size_bytes(self) -> u32 {
        CAbi::SUPPORTED.size_and_alignment(self).0
    }

    /// The same type with any `long long` rank replaced by `long`. Use it
    /// wherever only representation matters: arithmetic, value conversion,
    /// and matching a Click specification type (`int64`, `uint64`) against
    /// a C type of either rank.
    pub fn erase_long_rank(self) -> Self {
        const L: LongRank = LongRank::Long;
        match self {
            Self::Int64(_) => Self::Int64(L),
            Self::UInt64(_) => Self::UInt64(L),
            Self::Int64Pointer(_) => Self::Int64Pointer(L),
            Self::UInt64Pointer(_) => Self::UInt64Pointer(L),
            Self::Int64PointerPointer(_) => Self::Int64PointerPointer(L),
            Self::UInt64PointerPointer(_) => Self::UInt64PointerPointer(L),
            Self::Int64Array(_, length) => Self::Int64Array(L, length),
            Self::UInt64Array(_, length) => Self::UInt64Array(L, length),
            Self::PointerArray(element, _, length) => Self::PointerArray(element, L, length),
            other => other,
        }
    }

    /// The `long`/`long long` rank of a 64-bit integer type or of the
    /// element type of its pointer, pointer-pointer, or array forms.
    pub fn long_rank(self) -> Option<LongRank> {
        match self {
            Self::Int64(rank)
            | Self::UInt64(rank)
            | Self::Int64Pointer(rank)
            | Self::UInt64Pointer(rank)
            | Self::Int64PointerPointer(rank)
            | Self::UInt64PointerPointer(rank)
            | Self::Int64Array(rank, _)
            | Self::UInt64Array(rank, _) => Some(rank),
            Self::PointerArray(element, rank, _) => {
                pointer_array_element_type(element, rank).long_rank()
            }
            _ => None,
        }
    }

    /// Whether two types are the same but for `long`/`long long` rank:
    /// same representation, yet distinct, incompatible C types.
    pub fn differs_only_in_long_rank(self, other: Self) -> bool {
        self != other && self.erase_long_rank() == other.erase_long_rank()
    }
}

impl ImportedFunction {
    /// An explicitly declared one-call proof, represented with ordinary C AST nodes.
    pub(crate) fn with_proof_body(mut self, body: C0Statement) -> Self {
        self.body = body;
        self
    }

    pub(crate) fn with_return_pointee_constant(mut self, constant: bool) -> Self {
        self.return_pointee_constant = constant;
        self
    }

    pub(crate) fn with_return_reference(mut self, reference: bool) -> Self {
        self.return_reference = reference;
        self
    }

    pub(crate) fn with_read_only_contract(mut self, required: bool) -> Self {
        self.requires_read_only_contract = required;
        self
    }

    /// A declaration whose parameters are known only by position.
    pub(crate) fn with_positional_parameters(mut self) -> Self {
        self.positional_parameters = true;
        self
    }

    /// A crate trait method's implementation of `interface`.
    pub(crate) fn with_trait_interface(mut self, interface: Option<String>) -> Self {
        self.trait_interface = interface;
        self
    }

    /// The interface function this function implements, when it is a crate
    /// trait method's implementation.
    pub(crate) fn trait_interface(&self) -> Option<&str> {
        self.trait_interface.as_deref()
    }

    /// An instance of the generic function `generic`.
    pub(crate) fn with_generic_instance(mut self, generic: Option<String>) -> Self {
        self.generic_instance = generic;
        self
    }

    /// The generic function this declaration is an instance of.
    pub(crate) fn generic_instance(&self) -> Option<&str> {
        self.generic_instance.as_deref()
    }

    /// This C++ function, calling methods on receivers that may be objects of
    /// derived classes.
    pub(crate) fn with_receiver_calls(mut self, calls: Vec<(String, Option<String>)>) -> Self {
        self.receiver_calls = calls;
        self
    }

    /// Its calls of methods on receivers that may be objects of derived
    /// classes.
    pub(crate) fn receiver_calls(&self) -> &[(String, Option<String>)] {
        &self.receiver_calls
    }

    /// The C++ virtual method this function, a dispatch, stands for.
    pub(crate) fn dispatched_method(&self) -> Option<&str> {
        self.dispatched_method.as_deref()
    }

    /// A closure's function whose first `count` parameters are captures.
    pub(crate) fn with_closure_captures(mut self, count: usize) -> Self {
        self.closure_captures = count;
        self
    }

    /// The parameters that are a closure's captures; empty for any other
    /// function.
    pub(crate) fn closure_captures(&self) -> &[ImportedParameter] {
        &self.parameters[..self.closure_captures.min(self.parameters.len())]
    }

    pub(crate) fn has_positional_parameters(&self) -> bool {
        self.positional_parameters
    }

    /// This declaration with its positional parameters named as a sidecar
    /// head names them, or `None` when its parameters have their own names
    /// or the head has a different arity. Types stay the declaration's, so
    /// the head is still checked against them.
    pub(crate) fn named_by_head<'n>(
        &self,
        names: impl ExactSizeIterator<Item = &'n str>,
    ) -> Option<Self> {
        if !self.positional_parameters || names.len() != self.parameters.len() {
            return None;
        }
        let mut named = self.clone();
        for (parameter, name) in named.parameters.iter_mut().zip(names) {
            parameter.name = name.to_string();
        }
        named.positional_parameters = false;
        Some(named)
    }

    pub(crate) fn requires_read_only_contract(&self) -> bool {
        self.requires_read_only_contract
    }

    pub fn returns_reference(&self) -> bool {
        self.return_reference
    }

    pub fn return_pointee_is_constant(&self) -> bool {
        self.return_pointee_constant
    }

    /// A declaration with this function's interface and no body, named
    /// `name`: the dispatch a C++ importer names for a virtual method.
    pub(crate) fn external_alias(&self, name: String) -> Self {
        let mut alias = Self::external(self.return_type, name, self.parameters.clone());
        alias.return_pointee_constant = self.return_pointee_constant;
        alias.return_reference = self.return_reference;
        alias.return_struct_name = self.return_struct_name.clone();
        alias.return_pointer_struct_name = self.return_pointer_struct_name.clone();
        alias.requires_read_only_contract = self.requires_read_only_contract;
        alias.dispatched_method = Some(self.name.clone());
        alias
    }

    pub(crate) fn external(
        return_type: InterfaceType,
        name: String,
        parameters: Vec<ImportedParameter>,
    ) -> Self {
        Self {
            return_type,
            return_pointee_constant: false,
            return_reference: false,
            return_struct_name: None,
            aggregate_return_mode: crate::kernel::AggregateReturnMode::Copy,
            return_pointer_struct_name: None,
            source_name: name.clone(),
            name,
            inline_body: false,
            requires_read_only_contract: false,
            positional_parameters: false,
            closure_captures: 0,
            trait_interface: None,
            generic_instance: None,
            dispatched_method: None,
            receiver_calls: Vec::new(),
            program_entry_state: None,
            prelowered_kernel_function: None,
            parameters,
            body: C0Statement::Skip,
            callback_statement_sources: std::sync::Arc::default(),
            control_targets: BTreeMap::new(),
            structs: DeclarationMap::new(),
            enums: DeclarationMap::new(),
            unions: DeclarationMap::new(),
            globals: DeclarationMap::new(),
            global_arrays: DeclarationMap::new(),
            global_aggregates: DeclarationMap::new(),
            global_aggregate_arrays: DeclarationMap::new(),
            static_locals: BTreeMap::new(),
            static_arrays: BTreeMap::new(),
            static_aggregates: BTreeMap::new(),
            static_aggregate_arrays: BTreeMap::new(),
            local_struct_pointers: BTreeMap::new(),
            local_struct_values: BTreeMap::new(),
            local_references: BTreeSet::new(),
            local_pointers: BTreeSet::new(),
            string_literals: Vec::new(),
            loop_iterators: Vec::new(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn callback_statement_sources(
        &self,
    ) -> &std::sync::Arc<BTreeMap<String, C0Expression>> {
        &self.callback_statement_sources
    }

    pub fn source_name(&self) -> &str {
        &self.source_name
    }

    pub fn parameters(&self) -> &[ImportedParameter] {
        &self.parameters
    }

    /// This declaration with contract value parameters after its C
    /// parameters, so a contract that reads them lowers as it lowers the C
    /// parameters. The lowered function moves them back out of its C
    /// parameters ([`crate::kernel::ProgramFunction::with_trailing_value_parameters`]).
    pub(crate) fn with_trailing_value_parameters(
        &self,
        parameters: impl IntoIterator<Item = ImportedParameter>,
    ) -> Self {
        let mut function = self.clone();
        function.parameters.extend(parameters);
        function
    }

    pub fn return_type(&self) -> InterfaceType {
        self.return_type
    }

    pub fn return_struct_name(&self) -> Option<&str> {
        self.return_struct_name.as_deref()
    }

    pub fn return_pointer_struct_name(&self) -> Option<&str> {
        self.return_pointer_struct_name.as_deref()
    }

    pub fn body(&self) -> &C0Statement {
        &self.body
    }

    pub(crate) fn with_prelowered_kernel_function(
        mut self,
        function: crate::kernel::ProgramFunction,
    ) -> Self {
        // A front end that lowers its own body, as Rust's does, declares its
        // locals there; a sidecar comparison doing arithmetic on a pointer
        // one keeps its C meaning, as a C function's does.
        if self.local_pointers.is_empty() {
            self.local_pointers = declared_pointer_locals(function.body());
        }
        self.prelowered_kernel_function = Some(function);
        self
    }

    pub(crate) fn prelowered_kernel_function(&self) -> Option<&crate::kernel::ProgramFunction> {
        self.prelowered_kernel_function.as_ref()
    }

    /// Whether `self` and `other` are the same definition apart from how
    /// their callers use them: whether a caller observes a call inside an
    /// expression, which requires a read-only contract.
    pub(crate) fn same_definition_apart_from_uses(&self, other: &Self) -> bool {
        let mut other = other.clone();
        other.requires_read_only_contract = self.requires_read_only_contract;
        *self == other
    }

    /// Whether `self` and `other` declare the same interface: what a call
    /// through either binds, whatever each names its parameters. Two
    /// translation units of one project may each declare a function in
    /// their own words.
    pub(crate) fn declares_same_interface(&self, other: &Self) -> bool {
        let unnamed = |parameters: &[ImportedParameter]| {
            parameters
                .iter()
                .map(|parameter| ImportedParameter {
                    name: String::new(),
                    ..parameter.clone()
                })
                .collect::<Vec<_>>()
        };
        self.name == other.name
            && self.source_name == other.source_name
            && self.return_type == other.return_type
            && self.return_pointee_constant == other.return_pointee_constant
            && self.return_reference == other.return_reference
            && self.return_struct_name == other.return_struct_name
            && self.aggregate_return_mode == other.aggregate_return_mode
            && self.return_pointer_struct_name == other.return_pointer_struct_name
            && self.positional_parameters == other.positional_parameters
            && self.closure_captures == other.closure_captures
            && unnamed(&self.parameters) == unnamed(&other.parameters)
    }

    /// The name and construction-return mode of the kernel function
    /// [`Self::to_kernel_function`] builds, without lowering its body.
    pub(crate) fn kernel_name(&self) -> &str {
        self.prelowered_kernel_function
            .as_ref()
            .map_or(&self.name, |function| function.name())
    }

    pub(crate) fn returns_by_construction(&self) -> bool {
        match &self.prelowered_kernel_function {
            Some(function) => {
                function.contract_interface().aggregate_return_mode()
                    == crate::kernel::AggregateReturnMode::Construction
            }
            None => {
                self.return_struct_name.is_some()
                    && self.aggregate_return_mode
                        == crate::kernel::AggregateReturnMode::Construction
            }
        }
    }

    pub fn structs(&self) -> &DeclarationMap<RecordLayout> {
        &self.structs
    }

    pub fn enums(&self) -> &DeclarationMap<C0EnumDefinition> {
        &self.enums
    }

    pub fn unions(&self) -> &DeclarationMap<C0UnionLayout> {
        &self.unions
    }

    pub fn globals(&self) -> &DeclarationMap<C0Global> {
        &self.globals
    }

    pub fn global_arrays(&self) -> &DeclarationMap<C0GlobalArray> {
        &self.global_arrays
    }

    pub fn global_aggregates(&self) -> &DeclarationMap<C0GlobalAggregate> {
        &self.global_aggregates
    }

    pub fn global_aggregate_arrays(&self) -> &DeclarationMap<C0GlobalAggregateArray> {
        &self.global_aggregate_arrays
    }

    /// The struct name of each automatic local of struct-pointer type, by its
    /// C spelling.
    pub fn local_struct_pointers(&self) -> &BTreeMap<String, String> {
        &self.local_struct_pointers
    }

    pub(crate) fn with_local_struct_values(mut self, values: BTreeMap<String, String>) -> Self {
        self.local_struct_values = values;
        self
    }

    /// A foreign adapter's struct-pointer result, a C++ `Node*`: its
    /// contract reads `result->field` through the struct's layout.
    pub(crate) fn with_struct_pointer_return(mut self, name: String, layout: RecordLayout) -> Self {
        self.return_type = InterfaceType::Int32Pointer;
        self.structs.insert(name.clone(), layout);
        self.return_pointer_struct_name = Some(name);
        self
    }

    /// Preserve a foreign adapter's by-value return identity for sidecar checks.
    pub(crate) fn with_struct_return(mut self, name: String, layout: RecordLayout) -> Self {
        self.return_type = record_value_type(&layout);
        self.structs.insert(name.clone(), layout);
        self.return_struct_name = Some(name);
        self
    }

    pub(crate) fn with_aggregate_return_mode(
        mut self,
        mode: crate::kernel::AggregateReturnMode,
    ) -> Self {
        self.aggregate_return_mode = mode;
        self
    }

    pub fn local_struct_values(&self) -> &BTreeMap<String, String> {
        &self.local_struct_values
    }

    pub(crate) fn with_loop_iterators(mut self, iterators: Vec<Option<RustLoopIterator>>) -> Self {
        self.loop_iterators = iterators;
        self
    }

    /// The iterator each loop advances, by loop index, for a Rust function.
    pub fn loop_iterators(&self) -> &[Option<RustLoopIterator>] {
        &self.loop_iterators
    }

    pub(crate) fn with_local_references(mut self, references: BTreeSet<String>) -> Self {
        self.local_references = references;
        self
    }

    /// The automatic locals of reference type, by source name. A proof names
    /// one as it names a reference parameter: the name is the referent.
    pub fn local_references(&self) -> &BTreeSet<String> {
        &self.local_references
    }

    pub fn local_pointers(&self) -> &BTreeSet<String> {
        &self.local_pointers
    }

    pub fn string_literals(&self) -> &[C0StringLiteral] {
        &self.string_literals
    }

    pub(crate) fn with_globals(mut self, globals: DeclarationMap<C0Global>) -> Self {
        self.globals = globals;
        self
    }

    pub(crate) fn with_global_arrays(
        mut self,
        global_arrays: DeclarationMap<C0GlobalArray>,
    ) -> Self {
        self.global_arrays = global_arrays;
        self
    }

    pub(crate) fn with_global_aggregates(
        mut self,
        global_aggregates: DeclarationMap<C0GlobalAggregate>,
    ) -> Self {
        self.global_aggregates = global_aggregates;
        self
    }

    pub(crate) fn with_global_aggregate_arrays(
        mut self,
        global_aggregate_arrays: DeclarationMap<C0GlobalAggregateArray>,
    ) -> Self {
        self.global_aggregate_arrays = global_aggregate_arrays;
        self
    }

    pub fn body_kernel_statement(&self) -> crate::kernel::ProgramStatement {
        self.body
            .to_kernel_statement_with_control_targets(&self.control_targets)
    }

    pub(crate) fn control_targets(
        &self,
    ) -> &BTreeMap<String, (crate::kernel::ControlTargetId, usize)> {
        &self.control_targets
    }
}

impl RecordLayout {
    /// The struct's class for the strict-aliasing check, when it has one
    /// (`design/effective-types.md`).
    pub(crate) fn class(&self) -> Option<&crate::kernel::effective_type::CStructClass> {
        self.class.as_ref()
    }

    /// Constructs the proof-facing view of a flat, compiler-laid-out record.
    ///
    /// This is intentionally narrower than the C parser's aggregate builder:
    /// the initial C++ object slice admits only scalar `int` and `int*` fields
    /// and carries their already-decided ABI offsets across the frontend
    /// boundary without reconstructing source text.
    #[cfg(test)]
    pub(crate) fn from_explicit_fields(
        fields: Vec<(String, InterfaceType, u32, u32)>,
        size_bytes: u32,
        alignment_bytes: u32,
    ) -> Result<Self, String> {
        Self::from_explicit_fields_with_structs(
            fields
                .into_iter()
                .map(|(name, kind, offset, width)| (name, kind, None, offset, width))
                .collect(),
            size_bytes,
            alignment_bytes,
            &BTreeMap::new(),
        )
    }

    /// Marks a pointer field's pointee const, as an imported record's
    /// `const T*` field is: reads through it are allowed, writes refused.
    pub(crate) fn mark_pointee_constant(&mut self, name: &str) -> Result<(), String> {
        let field = self
            .fields
            .get_mut(name)
            .filter(|field| field.interface_type.is_pointer())
            .ok_or_else(|| format!("explicit struct field `{name}` is not a pointer"))?;
        field.pointee_constant = true;
        Ok(())
    }

    /// Imported embedded declarations use the same nominal field metadata and
    /// physical leaf layout as C structs. Bound materialized leaves before copying
    /// any nested layout, including a shared declaration used more than once.
    pub(crate) fn from_explicit_fields_with_structs(
        fields: Vec<(String, InterfaceType, Option<String>, u32, u32)>,
        size_bytes: u32,
        alignment_bytes: u32,
        structs: &BTreeMap<String, Self>,
    ) -> Result<Self, String> {
        const MAX_EXPLICIT_LAYOUT_LEAVES: usize = 65_536;
        // A layout may name no field: a C++ polymorphic class whose only
        // state is its vtable pointer, which no contract reads.
        if size_bytes == 0
            || alignment_bytes == 0
            || !alignment_bytes.is_power_of_two()
            || !size_bytes.is_multiple_of(alignment_bytes)
        {
            return Err("explicit struct layout has invalid size or alignment".into());
        }
        let mut named_fields = BTreeMap::new();
        let mut aggregate_fields = Vec::with_capacity(fields.len());
        let mut previous_end = 0u32;
        for (name, interface_type, struct_name, offset_bytes, byte_width) in fields {
            // A pointer field's struct name is its pointee's, as a C
            // `struct node *next` field's is: it embeds nothing, so the
            // pointee may be this struct itself.
            let nested = struct_name
                .as_ref()
                .filter(|_| interface_type != InterfaceType::Int32Pointer)
                .map(|name| {
                    structs
                        .get(name)
                        .ok_or_else(|| format!("unknown explicit embedded struct `{name}`"))
                })
                .transpose()?;
            let (expected_width, expected_alignment) = if let Some(layout) = nested {
                if interface_type != InterfaceType::Int32 || !layout.aggregate_unions.is_empty() {
                    return Err(format!(
                        "explicit embedded struct field `{name}` has unsupported storage"
                    ));
                }
                (layout.size_bytes, layout.alignment_bytes)
            } else {
                match interface_type {
                    InterfaceType::Int32Array(length) | InterfaceType::UInt32Array(length) => (
                        length
                            .checked_mul(4)
                            .filter(|width| *width <= i32::MAX as u32)
                            .ok_or_else(|| {
                                format!(
                                    "explicit struct field `{name}` array exceeds modeled storage"
                                )
                            })?,
                        4,
                    ),
                    InterfaceType::UInt8Array(length) if length <= i32::MAX as u32 => (length, 1),
                    InterfaceType::UInt8 => (1, 1),
                    InterfaceType::Int64(_) | InterfaceType::UInt64(_) => (8, 8),
                    InterfaceType::UInt16 => (2, 2),
                    InterfaceType::Int32 | InterfaceType::UInt32 => (4, 4),
                    // A value of an abstract type parameter, a generic Rust
                    // struct's field, at its model width.
                    InterfaceType::Parameter(_) => (
                        crate::kernel::ABSTRACT_VALUE_WIDTH,
                        crate::kernel::ABSTRACT_VALUE_WIDTH,
                    ),
                    InterfaceType::Int32Pointer
                    | InterfaceType::UInt8Pointer
                    | InterfaceType::UInt16Pointer
                    | InterfaceType::UInt32Pointer => (8, 8),
                    _ => {
                        return Err(format!(
                            "explicit struct field `{name}` has unsupported type"
                        ));
                    }
                }
            };
            let end = offset_bytes
                .checked_add(byte_width)
                .ok_or_else(|| format!("explicit struct field `{name}` layout overflows"))?;
            if name.is_empty()
                || byte_width != expected_width
                || alignment_bytes < expected_alignment
                || offset_bytes % expected_alignment != 0
                || (byte_width != 0 && offset_bytes < previous_end)
                || end > size_bytes
            {
                return Err(format!("explicit struct field `{name}` has invalid layout"));
            }
            if named_fields
                .insert(
                    name.clone(),
                    RecordField {
                        interface_type,
                        long_double: false,
                        pointee_constant: false,
                        struct_name,
                        enum_name: None,
                        union_name: None,
                        function_pointer_signature: None,
                        array_element_width: match interface_type {
                            InterfaceType::Int32Array(_) | InterfaceType::UInt32Array(_) => Some(4),
                            InterfaceType::UInt8Array(_) => Some(1),
                            _ => None,
                        },
                        array_shape: match interface_type {
                            InterfaceType::Int32Array(n)
                            | InterfaceType::UInt32Array(n)
                            | InterfaceType::UInt8Array(n) => Some(vec![n]),
                            _ => None,
                        },
                        offset_bytes,
                        byte_width,
                    },
                )
                .is_some()
            {
                return Err(format!("duplicate explicit struct field `{name}`"));
            }
            let added = nested.map_or(1, |layout| layout.aggregate_fields.len());
            if aggregate_fields.len().saturating_add(added) > MAX_EXPLICIT_LAYOUT_LEAVES {
                return Err(
                    "explicit struct layout exceeds the materialized leaf budget (65536)".into(),
                );
            }
            if let Some(layout) = nested {
                for field in &layout.aggregate_fields {
                    crate::instrumentation::record_deterministic_work(1);
                    aggregate_fields.push(RecordScalarField {
                        pointee_constant: field.pointee_constant,
                        name: format!("{name}.{}", field.name),
                        offset_bytes: offset_bytes
                            .checked_add(field.offset_bytes)
                            .ok_or("explicit embedded field offset overflows")?,
                        interface_type: field.interface_type,
                    });
                }
            } else {
                aggregate_fields.push(RecordScalarField {
                    pointee_constant: false,
                    name,
                    offset_bytes,
                    interface_type,
                });
            }
            previous_end = previous_end.max(end);
        }
        Ok(Self {
            fields: named_fields,
            aggregate_fields,
            aggregate_unions: Vec::new(),
            size_bytes,
            alignment_bytes,
            class: None,
        })
    }

    pub fn fields(&self) -> &BTreeMap<String, RecordField> {
        &self.fields
    }

    pub fn field(&self, name: &str) -> Option<&RecordField> {
        self.fields.get(name)
    }

    pub fn size_bytes(&self) -> u32 {
        self.size_bytes
    }

    pub fn alignment_bytes(&self) -> u32 {
        self.alignment_bytes
    }

    pub(crate) fn to_kernel_aggregate_layout(&self) -> crate::kernel::AggregateLayout {
        crate::kernel::AggregateLayout::with_unions(
            self.size_bytes,
            self.alignment_bytes,
            self.aggregate_fields
                .iter()
                .map(|field| {
                    crate::kernel::AggregateField::new(
                        &field.name,
                        field.offset_bytes,
                        field.interface_type.to_kernel_type(),
                    )
                    .with_array_shape(
                        self.fields
                            .get(&field.name)
                            .and_then(|declared| declared.array_shape()),
                    )
                })
                .collect(),
            self.aggregate_unions
                .iter()
                .map(|union| {
                    crate::kernel::AggregateUnion::new(
                        &union.name,
                        union.offset_bytes,
                        union.size_bytes,
                        union
                            .fields
                            .iter()
                            .map(|field| {
                                crate::kernel::AggregateUnionField::new(
                                    &field.name,
                                    field.offset_bytes,
                                    field.interface_type.to_kernel_type(),
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        )
    }

    pub(super) fn aggregate_fields(&self) -> &[RecordScalarField] {
        &self.aggregate_fields
    }

    /// The byte runs that hold values: each scalar leaf at its offset, and
    /// each union's storage whole. The rest of the struct is padding, or the
    /// implicit vtable pointer of a C++ polymorphic class.
    pub(crate) fn value_byte_runs(&self) -> Vec<(u32, u32)> {
        self.aggregate_fields
            .iter()
            .map(|field| {
                (
                    field.offset_bytes,
                    field.interface_type.to_kernel_type().byte_width(),
                )
            })
            .chain(
                self.aggregate_unions
                    .iter()
                    .map(|union| (union.offset_bytes, union.size_bytes)),
            )
            .collect()
    }

    /// Scalar leaves with their declared types, including embedded fields.
    pub(crate) fn typed_leaf_fields(&self) -> impl Iterator<Item = (&str, u32, InterfaceType)> {
        self.aggregate_fields.iter().map(|field| {
            (
                field.name.as_str(),
                field.offset_bytes,
                field.interface_type,
            )
        })
    }

    /// Each scalar leaf of the struct with its byte offset, embedded struct
    /// fields flattened to qualified paths such as `inner.count`.
    pub(crate) fn leaf_field_offsets(&self) -> impl Iterator<Item = (&str, u32)> {
        self.aggregate_fields
            .iter()
            .map(|field| (field.name.as_str(), field.offset_bytes))
    }
}

impl RecordField {
    pub fn is_long_double(&self) -> bool {
        self.long_double
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn offset_bytes(&self) -> u32 {
        self.offset_bytes
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn enum_name(&self) -> Option<&str> {
        self.enum_name.as_deref()
    }

    pub fn union_name(&self) -> Option<&str> {
        self.union_name.as_deref()
    }

    pub fn function_pointer_signature(&self) -> Option<&CallbackInterface> {
        self.function_pointer_signature.as_ref()
    }

    pub fn array_element_width(&self) -> Option<u32> {
        self.array_element_width
    }

    pub fn array_shape(&self) -> Option<&[u32]> {
        self.array_shape.as_deref()
    }

    pub fn byte_width(&self) -> u32 {
        self.byte_width
    }
}

impl ImportedParameter {
    /// Retain a declared pointer's nominal pointee for source presentation.
    pub(crate) fn with_pointee_struct_layout(mut self, name: String, layout: RecordLayout) -> Self {
        assert!(self.interface_type.is_pointer());
        self.struct_name = Some(name);
        self.pointee_struct_layout = Some(layout);
        self
    }

    pub(crate) fn with_slice_length_parameter(mut self, parameter: usize) -> Self {
        self.slice_length_parameter = Some(parameter);
        self
    }

    pub(crate) fn with_fixed_reference_extent(mut self, bytes: u32) -> Self {
        self.fixed_reference_extent = Some(bytes);
        self
    }

    pub(crate) fn with_struct_value(mut self, name: String, layout: RecordLayout) -> Self {
        self.interface_type = record_value_type(&layout);
        self.struct_name = Some(name);
        self.struct_layout = Some(layout);
        self
    }

    /// A function-pointer parameter, typed by its signature.
    pub(crate) fn function_pointer(name: String, signature: CallbackInterface) -> Self {
        let mut parameter = Self::new(signature.pointer_type(), name, None);
        parameter.function_pointer_signature = Some(signature);
        parameter
    }

    pub(crate) fn new(
        interface_type: InterfaceType,
        name: String,
        struct_name: Option<String>,
    ) -> Self {
        Self {
            interface_type,
            name,
            volatile: false,
            pointee_volatile: false,
            constant: false,
            pointee_constant: false,
            reference: false,
            struct_name,
            union_name: None,
            struct_layout: None,
            pointee_struct_layout: None,
            function_pointer_signature: None,
            array_element_width: None,
            pointee_struct_class: None,
            slice_length_parameter: None,
            fixed_reference_extent: None,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn interface_type(&self) -> InterfaceType {
        self.interface_type
    }

    pub fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub fn is_constant(&self) -> bool {
        self.constant
    }

    pub fn pointee_is_constant(&self) -> bool {
        self.pointee_constant
    }

    pub(crate) fn with_constant(mut self, constant: bool) -> Self {
        self.constant = constant;
        self
    }

    pub(crate) fn with_pointee_constant(mut self, pointee_constant: bool) -> Self {
        self.pointee_constant = pointee_constant;
        self
    }

    pub fn is_reference(&self) -> bool {
        self.reference
    }

    pub(crate) fn with_reference(mut self, reference: bool) -> Self {
        self.reference = reference;
        self
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }

    pub fn union_name(&self) -> Option<&str> {
        self.union_name.as_deref()
    }

    pub fn struct_layout(&self) -> Option<&RecordLayout> {
        self.struct_layout.as_ref()
    }

    pub fn pointee_struct_layout(&self) -> Option<&RecordLayout> {
        self.pointee_struct_layout.as_ref()
    }

    pub fn array_element_width(&self) -> Option<u32> {
        self.array_element_width
    }

    pub fn function_pointer_signature(&self) -> Option<&CallbackInterface> {
        self.function_pointer_signature.as_ref()
    }

    pub fn is_struct_value(&self) -> bool {
        self.struct_name.is_some() && matches!(self.interface_type, InterfaceType::UInt8Array(_))
    }
}

impl InterfaceType {
    /// The length of an array type; `None` for any other type.
    pub fn array_length(self) -> Option<u32> {
        match self {
            Self::CharArray(_, length)
            | Self::Int32Array(length)
            | Self::UInt8Array(length)
            | Self::Int8Array(length)
            | Self::Int16Array(length)
            | Self::UInt16Array(length)
            | Self::UInt32Array(length)
            | Self::Int64Array(_, length)
            | Self::Int128Array(length)
            | Self::UInt64Array(_, length)
            | Self::UInt128Array(length)
            | Self::Float32Array(length)
            | Self::Float64Array(length)
            | Self::PointerArray(_, _, length) => Some(length),
            _ => None,
        }
    }

    pub fn is_pointer(self) -> bool {
        matches!(
            self,
            Self::VoidPointer
                | Self::VoidPointerPointer
                | Self::Int32Pointer
                | Self::Int8Pointer
                | Self::Int16Pointer
                | Self::UInt16Pointer
                | Self::CharPointer(_)
                | Self::UInt8Pointer
                | Self::UInt32Pointer
                | Self::Int128Pointer
                | Self::Int64Pointer(_)
                | Self::UInt128Pointer
                | Self::UInt64Pointer(_)
                | Self::Float32Pointer
                | Self::Float64Pointer
                | Self::Int8PointerPointer
                | Self::Int16PointerPointer
                | Self::UInt16PointerPointer
                | Self::Int32PointerPointer
                | Self::CharPointerPointer(_)
                | Self::UInt8PointerPointer
                | Self::UInt32PointerPointer
                | Self::Int128PointerPointer
                | Self::Int64PointerPointer(_)
                | Self::UInt128PointerPointer
                | Self::UInt64PointerPointer(_)
                | Self::Float32PointerPointer
                | Self::Float64PointerPointer
                | Self::FunctionPointer(_)
        )
    }

    pub fn is_object_pointer(self) -> bool {
        self.is_pointer() && !matches!(self, Self::FunctionPointer(_))
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Parameter(_) => None,
            Self::ParameterPointer(parameter) => Some(Self::Parameter(parameter)),
            Self::Int128 | Self::UInt128 => None,
            Self::CharPointer(plain) | Self::CharArray(plain, _) => Some(Self::Char(plain)),
            Self::Int8Pointer | Self::Int8Array(_) => Some(Self::Int8),
            Self::Int16Pointer | Self::Int16Array(_) => Some(Self::Int16),
            Self::Int32Pointer | Self::Int32Array(_) => Some(Self::Int32),
            Self::UInt8Pointer | Self::UInt8Array(_) => Some(Self::UInt8),
            Self::UInt16Pointer | Self::UInt16Array(_) => Some(Self::UInt16),
            Self::UInt32Pointer | Self::UInt32Array(_) => Some(Self::UInt32),
            Self::Int64Pointer(rank) | Self::Int64Array(rank, _) => Some(Self::Int64(rank)),
            Self::Int128Pointer | Self::Int128Array(_) => Some(Self::Int128),
            Self::UInt64Pointer(rank) | Self::UInt64Array(rank, _) => Some(Self::UInt64(rank)),
            Self::UInt128Pointer | Self::UInt128Array(_) => Some(Self::UInt128),
            Self::Float32Pointer | Self::Float32Array(_) => Some(Self::Float32),
            Self::Float64Pointer | Self::Float64Array(_) => Some(Self::Float64),
            Self::PointerArray(element, rank, _) => Some(pointer_array_element_type(element, rank)),
            Self::Int8PointerPointer => Some(Self::Int8Pointer),
            Self::Int16PointerPointer => Some(Self::Int16Pointer),
            Self::UInt16PointerPointer => Some(Self::UInt16Pointer),
            Self::Int32PointerPointer => Some(Self::Int32Pointer),
            Self::CharPointerPointer(plain) => Some(Self::CharPointer(plain)),
            Self::UInt8PointerPointer => Some(Self::UInt8Pointer),
            Self::UInt32PointerPointer => Some(Self::UInt32Pointer),
            Self::Int64PointerPointer(rank) => Some(Self::Int64Pointer(rank)),
            Self::Int128PointerPointer => Some(Self::Int128Pointer),
            Self::UInt64PointerPointer(rank) => Some(Self::UInt64Pointer(rank)),
            Self::UInt128PointerPointer => Some(Self::UInt128Pointer),
            Self::Float32PointerPointer => Some(Self::Float32Pointer),
            Self::Float64PointerPointer => Some(Self::Float64Pointer),
            Self::VoidPointerPointer => Some(Self::VoidPointer),
            Self::Int8 => None,
            Self::Void
            | Self::VoidPointer
            | Self::Bool
            | Self::Int16
            | Self::Int32
            | Self::Char(_)
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::Int64(_)
            | Self::UInt64(_)
            | Self::Float32
            | Self::Float64
            | Self::FunctionPointer(_) => None,
        }
    }

    pub(crate) fn pointer_type(self) -> Option<Self> {
        Some(match self {
            Self::Parameter(parameter) => Self::ParameterPointer(parameter),
            Self::ParameterPointer(_) => return None,
            Self::Int8 => Self::Int8Pointer,
            Self::Int16 => Self::Int16Pointer,
            Self::Int32 => Self::Int32Pointer,
            Self::Char(plain) => Self::CharPointer(plain),
            Self::UInt8 => Self::UInt8Pointer,
            Self::UInt16 => Self::UInt16Pointer,
            Self::UInt32 => Self::UInt32Pointer,
            Self::Int64(rank) => Self::Int64Pointer(rank),
            Self::Int128 => Self::Int128Pointer,
            Self::UInt64(rank) => Self::UInt64Pointer(rank),
            Self::UInt128 => Self::UInt128Pointer,
            Self::Float32 => Self::Float32Pointer,
            Self::Float64 => Self::Float64Pointer,
            Self::Int8Pointer => Self::Int8PointerPointer,
            Self::Int16Pointer => Self::Int16PointerPointer,
            Self::UInt16Pointer => Self::UInt16PointerPointer,
            Self::Int32Pointer => Self::Int32PointerPointer,
            Self::CharPointer(plain) => Self::CharPointerPointer(plain),
            Self::UInt8Pointer => Self::UInt8PointerPointer,
            Self::UInt32Pointer => Self::UInt32PointerPointer,
            Self::Int64Pointer(rank) => Self::Int64PointerPointer(rank),
            Self::Int128Pointer => Self::Int128PointerPointer,
            Self::UInt64Pointer(rank) => Self::UInt64PointerPointer(rank),
            Self::UInt128Pointer => Self::UInt128PointerPointer,
            Self::Float32Pointer => Self::Float32PointerPointer,
            Self::Float64Pointer => Self::Float64PointerPointer,
            Self::VoidPointer => Self::VoidPointerPointer,
            Self::Int8PointerPointer | Self::Int8Array(_) => return None,
            Self::Void
            | Self::VoidPointerPointer
            | Self::Bool
            | Self::Int16PointerPointer
            | Self::UInt16PointerPointer
            | Self::Int32PointerPointer
            | Self::CharPointerPointer(_)
            | Self::UInt8PointerPointer
            | Self::UInt32PointerPointer
            | Self::Int128PointerPointer
            | Self::Int64PointerPointer(_)
            | Self::UInt128PointerPointer
            | Self::UInt64PointerPointer(_)
            | Self::Float32PointerPointer
            | Self::Float64PointerPointer
            | Self::FunctionPointer(_)
            | Self::Int32Array(_)
            | Self::CharArray(_, _)
            | Self::UInt8Array(_)
            | Self::Int16Array(_)
            | Self::UInt16Array(_)
            | Self::UInt32Array(_)
            | Self::Int128Array(_)
            | Self::Int64Array(_, _)
            | Self::UInt128Array(_)
            | Self::UInt64Array(_, _)
            | Self::Float32Array(_)
            | Self::Float64Array(_) => return None,
            Self::PointerArray(_, _, _) => return None,
        })
    }

    /// The kernel type of a pointer to a byte type (`uint8` or `int8`).
    pub(super) fn pointer_kernel_type(self) -> crate::kernel::ProgramType {
        match self {
            Self::Int8 => crate::kernel::ProgramType::Int8Pointer,
            _ => crate::kernel::ProgramType::UInt8Pointer,
        }
    }

    /// The kernel type of a value of this C type. Plain `char` types take
    /// the representation of their target's [`PlainChar::byte_type`], so
    /// this mapping needs no target of its own.
    pub fn to_kernel_type(self) -> crate::kernel::ProgramType {
        match self {
            Self::Parameter(name) => crate::kernel::ProgramType::Parameter(name),
            Self::ParameterPointer(name) => crate::kernel::ProgramType::ParameterPointer(name),
            Self::Void => crate::kernel::ProgramType::Void,
            Self::Bool => crate::kernel::ProgramType::Bool,
            Self::VoidPointer => crate::kernel::ProgramType::VoidPointer,
            Self::VoidPointerPointer => crate::kernel::ProgramType::VoidPointerPointer,
            Self::Int8 => crate::kernel::ProgramType::Int8,
            Self::Int16 => crate::kernel::ProgramType::Int16,
            Self::Int32 => crate::kernel::ProgramType::Int32,
            Self::Char(plain) => plain.byte_type().to_kernel_type(),
            Self::UInt8 => crate::kernel::ProgramType::UInt8,
            Self::UInt16 => crate::kernel::ProgramType::UInt16,
            Self::UInt32 => crate::kernel::ProgramType::UInt32,
            Self::Int64(_) => crate::kernel::ProgramType::Int64,
            Self::UInt64(_) => crate::kernel::ProgramType::UInt64,
            Self::Int128 => crate::kernel::ProgramType::Int128,
            Self::UInt128 => crate::kernel::ProgramType::UInt128,
            Self::Float32 => crate::kernel::ProgramType::Float32,
            Self::Float64 => crate::kernel::ProgramType::Float64,
            Self::Int32Pointer => crate::kernel::ProgramType::Int32Pointer,
            Self::Int8Pointer => crate::kernel::ProgramType::Int8Pointer,
            Self::Int16Pointer => crate::kernel::ProgramType::Int16Pointer,
            Self::UInt16Pointer => crate::kernel::ProgramType::UInt16Pointer,
            Self::CharPointer(plain) => plain.byte_type().pointer_kernel_type(),
            Self::UInt8Pointer => crate::kernel::ProgramType::UInt8Pointer,
            Self::UInt32Pointer => crate::kernel::ProgramType::UInt32Pointer,
            Self::Int64Pointer(_) => crate::kernel::ProgramType::Int64Pointer,
            Self::Int128Pointer => crate::kernel::ProgramType::Int128Pointer,
            Self::UInt64Pointer(_) => crate::kernel::ProgramType::UInt64Pointer,
            Self::UInt128Pointer => crate::kernel::ProgramType::UInt128Pointer,
            Self::Float32Pointer => crate::kernel::ProgramType::Float32Pointer,
            Self::Float64Pointer => crate::kernel::ProgramType::Float64Pointer,
            Self::Int8PointerPointer => crate::kernel::ProgramType::Int8PointerPointer,
            Self::Int16PointerPointer => crate::kernel::ProgramType::Int16PointerPointer,
            Self::UInt16PointerPointer => crate::kernel::ProgramType::UInt16PointerPointer,
            Self::Int32PointerPointer => crate::kernel::ProgramType::Int32PointerPointer,
            Self::CharPointerPointer(PlainChar::Unsigned) => {
                crate::kernel::ProgramType::UInt8PointerPointer
            }
            Self::CharPointerPointer(PlainChar::Signed) => {
                crate::kernel::ProgramType::Int8PointerPointer
            }
            Self::UInt8PointerPointer => crate::kernel::ProgramType::UInt8PointerPointer,
            Self::UInt32PointerPointer => crate::kernel::ProgramType::UInt32PointerPointer,
            Self::Int64PointerPointer(_) => crate::kernel::ProgramType::Int64PointerPointer,
            Self::Int128PointerPointer => crate::kernel::ProgramType::Int128PointerPointer,
            Self::UInt64PointerPointer(_) => crate::kernel::ProgramType::UInt64PointerPointer,
            Self::UInt128PointerPointer => crate::kernel::ProgramType::UInt128PointerPointer,
            Self::Float32PointerPointer => crate::kernel::ProgramType::Float32PointerPointer,
            Self::Float64PointerPointer => crate::kernel::ProgramType::Float64PointerPointer,
            Self::FunctionPointer(signature) => {
                crate::kernel::ProgramType::FunctionPointer(signature)
            }
            Self::Int32Array(length) => crate::kernel::ProgramType::Int32Array(length),
            Self::CharArray(PlainChar::Unsigned, length) => {
                crate::kernel::ProgramType::UInt8Array(length)
            }
            Self::CharArray(PlainChar::Signed, length) => {
                crate::kernel::ProgramType::Int8Array(length)
            }
            Self::UInt8Array(length) => crate::kernel::ProgramType::UInt8Array(length),
            Self::Int8Array(length) => crate::kernel::ProgramType::Int8Array(length),
            Self::Int16Array(length) => crate::kernel::ProgramType::Int16Array(length),
            Self::UInt16Array(length) => crate::kernel::ProgramType::UInt16Array(length),
            Self::UInt32Array(length) => crate::kernel::ProgramType::UInt32Array(length),
            Self::Int64Array(_, length) => crate::kernel::ProgramType::Int64Array(length),
            Self::Int128Array(length) => crate::kernel::ProgramType::Int128Array(length),
            Self::UInt64Array(_, length) => crate::kernel::ProgramType::UInt64Array(length),
            Self::UInt128Array(length) => crate::kernel::ProgramType::UInt128Array(length),
            Self::Float32Array(length) => crate::kernel::ProgramType::Float32Array(length),
            Self::Float64Array(length) => crate::kernel::ProgramType::Float64Array(length),
            Self::PointerArray(element, _, length) => {
                crate::kernel::ProgramType::PointerArray(element, length)
            }
        }
    }
}

pub(super) fn pointer_array_element_type(
    element: crate::kernel::PointerArrayElement,
    rank: LongRank,
) -> InterfaceType {
    use crate::kernel::PointerArrayElement as Element;
    match element {
        Element::Void => InterfaceType::VoidPointer,
        Element::UnsignedPlainChar => InterfaceType::CharPointer(PlainChar::Unsigned),
        Element::SignedPlainChar => InterfaceType::CharPointer(PlainChar::Signed),
        Element::UnsignedPlainCharPointer => InterfaceType::CharPointerPointer(PlainChar::Unsigned),
        Element::SignedPlainCharPointer => InterfaceType::CharPointerPointer(PlainChar::Signed),
        Element::Int8 => InterfaceType::Int8Pointer,
        Element::Int16 => InterfaceType::Int16Pointer,
        Element::Int32 => InterfaceType::Int32Pointer,
        Element::UInt8 => InterfaceType::UInt8Pointer,
        Element::UInt16 => InterfaceType::UInt16Pointer,
        Element::UInt32 => InterfaceType::UInt32Pointer,
        Element::Int64 => InterfaceType::Int64Pointer(rank),
        Element::Int128 => InterfaceType::Int128Pointer,
        Element::UInt64 => InterfaceType::UInt64Pointer(rank),
        Element::UInt128 => InterfaceType::UInt128Pointer,
        Element::Float32 => InterfaceType::Float32Pointer,
        Element::Float64 => InterfaceType::Float64Pointer,
    }
}

pub(super) fn record_value_type(layout: &RecordLayout) -> InterfaceType {
    InterfaceType::UInt8Array(layout.size_bytes)
}

pub(super) fn declared_pointer_locals(body: &crate::kernel::ProgramStatement) -> BTreeSet<String> {
    use crate::kernel::ProgramStatement;
    let mut pointers = BTreeMap::<String, bool>::new();
    let mut pending = vec![body];
    while let Some(statement) = pending.pop() {
        match statement {
            ProgramStatement::Declare {
                name, program_type, ..
            } => {
                let pointer = program_type.is_pointer();
                pointers
                    .entry(name.clone())
                    .and_modify(|existing| *existing &= pointer)
                    .or_insert(pointer);
            }
            ProgramStatement::Seq(statements) => {
                pending.extend(statements.iter().map(|item| &**item))
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
            }
            ProgramStatement::While { body, .. } => pending.push(body),
            ProgramStatement::ForStep { step, .. } => pending.push(step),
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                pending.push(try_body);
                pending.push(handler);
            }
            ProgramStatement::Switch { cases, .. } => {
                pending.extend(cases.iter().map(|case| &*case.body))
            }
            _ => {}
        }
    }
    pointers
        .into_iter()
        .filter_map(|(name, pointer)| pointer.then_some(name))
        .collect()
}

/// The iterator a Rust `for` loop advances: the local holding its state and
/// what it iterates.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct RustLoopIterator {
    pub local: String,
    pub kind: RustIteratorKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RustIteratorKind {
    /// `core::slice::Iter` or a shared array's iterator: `_cursor` and
    /// `_remaining` locals.
    Slice,
    /// `Enumerate<Iter<T>>`: the slice iterator's state and `_count`.
    Enumerate,
    /// `core::slice::Iter` in the library-iterator model: one local holding
    /// a value of the library's `SliceIter` at this type, which a proof
    /// names `iter` and reads with that type's methods.
    SliceLibrary(crate::kernel::TypeParameterName),
    /// `ChunksExact<u8>`: one local holding a value of the library's
    /// `ChunksExact<uint8>`, which a proof names `iter` and reads with that
    /// type's methods.
    Chunks,
    /// `Range`: `_start` and `_end`.
    Range,
    /// `RangeInclusive`: `_start`, `_end`, and `_done`, whether it has
    /// yielded its end.
    RangeInclusive,
}
