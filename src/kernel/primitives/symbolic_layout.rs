//! Layouts whose sizes and field offsets are terms: an instance of a generic
//! struct at an abstract type, `Cell<T>`, whose field of `T` takes
//! `sizeof(T)` bytes. Its size is `sizeof(Cell<T>)` and each field's offset is
//! `offsetof(Cell<T>, field)`, numbers the instance fixes and Click does not
//! know. A layout whose field sizes are known keeps numbers
//! (`docs/internals/kernel.md#symbolic-layouts`).
//!
//! The terms are opaque applications. What a language says of every layout,
//! that distinct fields of one object never share a byte and that each field
//! lies inside its object, is decided by looking the terms up here: two
//! accesses at one base through two fields of one layout, each reaching no
//! further than its field, are apart. No pairwise fact is stated.

use super::{MachineTerm, TypeParameterName};
use std::sync::{Arc, Mutex};

/// The bytes an access reaches: a fixed count from its address, or, for a
/// value of an abstract type, its whole object, `[p, p + sizeof(T))`,
/// whose size the type fixes and Click does not know.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AccessExtent {
    Bytes(u32),
    Object(TypeParameterName),
}

impl From<u32> for AccessExtent {
    fn from(bytes: u32) -> Self {
        Self::Bytes(bytes)
    }
}

impl std::fmt::Display for AccessExtent {
    /// A byte count, or `sizeof(T)`, as Surface spells it.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bytes(bytes) => write!(formatter, "{bytes}"),
            Self::Object(parameter) => write!(formatter, "sizeof({})", parameter.name()),
        }
    }
}

impl AccessExtent {
    /// The extent of a value of `program_type` held whole.
    pub fn of_type(program_type: super::ProgramType) -> Self {
        match program_type {
            super::ProgramType::Parameter(parameter) if parameter.has_abstract_size() => {
                Self::Object(parameter)
            }
            other => Self::Bytes(other.byte_width()),
        }
    }

    /// The extent of a value of `algebraic_type` read whole: its object,
    /// `sizeof(T)`, for a type Click knows only by name, and the model's
    /// width for an algebraic value it lays out itself.
    pub fn of_algebraic(algebraic_type: &super::AlgebraicType) -> Self {
        if algebraic_type.rigid
            && algebraic_type.arguments.is_empty()
            && algebraic_type.variants.is_empty()
            && let parameter = TypeParameterName::of(algebraic_type)
            && parameter.has_abstract_size()
        {
            Self::Object(parameter)
        } else {
            Self::Bytes(super::ABSTRACT_VALUE_WIDTH)
        }
    }

    /// The extent's byte count, when it is a number.
    pub fn bytes(self) -> Option<u32> {
        match self {
            Self::Bytes(bytes) => Some(bytes),
            Self::Object(_) => None,
        }
    }

    /// The extent as a 64-bit term: its count, or `sizeof(T)`.
    pub fn term(self) -> MachineTerm {
        match self {
            Self::Bytes(bytes) => MachineTerm::uint64_constant(u64::from(bytes)),
            Self::Object(parameter) => parameter.size_term(),
        }
    }
}

/// One registered symbolic layout.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SymbolicLayoutName(u32);

/// Where a field starts in its object: a number, or the field's
/// `offsetof` term in a symbolic layout.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LayoutOffset {
    Bytes(u32),
    Field(SymbolicLayoutName, u32),
}

impl From<u32> for LayoutOffset {
    fn from(bytes: u32) -> Self {
        Self::Bytes(bytes)
    }
}

impl std::fmt::Display for LayoutOffset {
    /// A number, or `offsetof(L, f)`, as Surface spells it.
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bytes(bytes) => write!(formatter, "{bytes}"),
            Self::Field(layout, field) => {
                write!(
                    formatter,
                    "offsetof({}, {})",
                    layout.name(),
                    layout.field_name(*field)
                )
            }
        }
    }
}

impl LayoutOffset {
    /// The offset's byte count, when it is a number.
    pub fn bytes(self) -> Option<u32> {
        match self {
            Self::Bytes(bytes) => Some(bytes),
            Self::Field(..) => None,
        }
    }

    /// The byte count of an offset in a concrete layout. Only code that has
    /// already refused symbolic layouts calls this.
    pub fn concrete(self) -> u32 {
        self.bytes()
            .expect("a byte offset of a concrete layout; symbolic layouts use their terms")
    }

    /// The offset as a 64-bit term.
    pub fn term(self) -> MachineTerm {
        match self {
            Self::Bytes(bytes) => MachineTerm::uint64_constant(u64::from(bytes)),
            Self::Field(layout, field) => layout.offset_term(field),
        }
    }
}

/// A size: a number, or the `sizeof` term of a symbolic layout.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum LayoutSize {
    Bytes(u32),
    Of(SymbolicLayoutName),
}

impl From<u32> for LayoutSize {
    fn from(bytes: u32) -> Self {
        Self::Bytes(bytes)
    }
}

impl LayoutSize {
    pub fn bytes(self) -> Option<u32> {
        match self {
            Self::Bytes(bytes) => Some(bytes),
            Self::Of(_) => None,
        }
    }

    pub fn concrete(self) -> u32 {
        self.bytes()
            .expect("the size of a concrete layout; symbolic layouts use their terms")
    }

    pub fn term(self) -> MachineTerm {
        match self {
            Self::Bytes(bytes) => MachineTerm::uint64_constant(u64::from(bytes)),
            Self::Of(layout) => layout.size_term(),
        }
    }
}

/// One field of a symbolic layout: its name, the type a cell of it holds
/// (none for an embedded record), the bytes it takes, and, for a field the
/// language places before any field whose size or alignment the layout's
/// abstract types fix, its byte offset.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicField {
    pub name: String,
    pub field_type: Option<super::ProgramType>,
    pub extent: AccessExtent,
    pub fixed_offset: Option<u32>,
}

impl SymbolicField {
    /// A field at an `offsetof` term holding a value of `field_type`.
    pub fn placed(name: String, field_type: super::ProgramType) -> Self {
        Self {
            name,
            field_type: Some(field_type),
            extent: AccessExtent::of_type(field_type),
            fixed_offset: None,
        }
    }
}

struct Entry {
    name: String,
    fields: Vec<(String, AccessExtent)>,
    field_types: Vec<Option<super::ProgramType>>,
    fixed_offsets: Vec<Option<u32>>,
    /// The bytes `[0, prefix_end)` the fixed fields lie in; every field at
    /// a term starts at or after it.
    prefix_end: u32,
    size_term: Arc<str>,
    offset_terms: Vec<Arc<str>>,
}

#[derive(Default)]
struct Registry {
    layouts: Vec<&'static Entry>,
    /// Each term name's layout, and its field for an offset.
    terms: std::collections::HashMap<Arc<str>, (SymbolicLayoutName, Option<u32>)>,
}

static LAYOUTS: Mutex<Option<Registry>> = Mutex::new(None);

fn with_registry<R>(f: impl FnOnce(&mut Registry) -> R) -> R {
    let mut guard = LAYOUTS.lock().expect("symbolic layouts");
    f(guard.get_or_insert_with(Registry::default))
}

impl SymbolicLayoutName {
    /// The layout of `name` with `fields` in declaration order, each a
    /// scalar, a pointer, or a value of an abstract type, every one at an
    /// `offsetof` term. One name and field list is one layout.
    pub fn intern(name: &str, typed_fields: Vec<(String, super::ProgramType)>) -> Self {
        Self::intern_fields(
            name,
            typed_fields
                .into_iter()
                .map(|(field, field_type)| SymbolicField::placed(field, field_type))
                .collect(),
            0,
        )
    }

    /// The layout of `name` with `fields` in declaration order, the fixed
    /// ones first: a language that places each field after the ones before
    /// it fixes the offsets up to the first field an abstract type sizes or
    /// aligns, and only the rest are terms. `reserved_prefix` bytes at the
    /// start belong to no field, as a polymorphic class's vtable pointer.
    pub fn intern_fields(
        name: &str,
        symbolic_fields: Vec<SymbolicField>,
        reserved_prefix: u32,
    ) -> Self {
        let field_types = symbolic_fields
            .iter()
            .map(|field| field.field_type)
            .collect::<Vec<_>>();
        let fixed_offsets = symbolic_fields
            .iter()
            .map(|field| field.fixed_offset)
            .collect::<Vec<_>>();
        let prefix_end = symbolic_fields
            .iter()
            .filter_map(|field| Some(field.fixed_offset? + field.extent.bytes()?))
            .max()
            .unwrap_or(0)
            .max(reserved_prefix);
        let fields = symbolic_fields
            .into_iter()
            .map(|field| (field.name, field.extent))
            .collect::<Vec<_>>();
        with_registry(|registry| {
            if let Some(index) = registry.layouts.iter().position(|known| {
                crate::instrumentation::record_deterministic_work(1);
                known.name == name
                    && known.field_types == field_types
                    && known.fixed_offsets == fixed_offsets
                    && known.prefix_end == prefix_end
                    && known.fields == fields
            }) {
                return Self(index as u32);
            }
            let id = Self(registry.layouts.len() as u32);
            // A second layout of one name, from another program, keeps
            // distinct terms.
            let suffix = if registry.layouts.iter().any(|known| known.name == name) {
                format!("#{}", id.0)
            } else {
                String::new()
            };
            // The size is the struct type's own `sizeof`, the one a value of
            // the type held whole reaches ([`Self::value_type`]).
            let MachineTerm::PureFunctionApplication {
                name: size_name, ..
            } = TypeParameterName::intern(name).size_term()
            else {
                unreachable!("a type's size term is an application")
            };
            let size_term: Arc<str> = size_name.into();
            let offset_terms = fields
                .iter()
                .map(|(field, _)| Arc::<str>::from(format!("offsetof<{name}{suffix}, {field}>")))
                .collect::<Vec<_>>();
            registry.terms.insert(size_term.clone(), (id, None));
            for (index, term) in offset_terms.iter().enumerate() {
                registry
                    .terms
                    .insert(term.clone(), (id, Some(index as u32)));
            }
            registry.layouts.push(Box::leak(Box::new(Entry {
                name: name.to_string(),
                fields,
                field_types,
                fixed_offsets,
                prefix_end,
                size_term,
                offset_terms,
            })));
            id
        })
    }

    fn entry(self) -> &'static Entry {
        with_registry(|registry| registry.layouts[self.0 as usize])
    }

    /// The type of a value of the struct held whole, a by-value argument or
    /// result: an object of the struct's size, whose fields this layout
    /// places.
    pub fn value_type(self) -> TypeParameterName {
        TypeParameterName::intern(self.name())
    }

    /// The struct type's name, as Surface spells it.
    pub fn name(self) -> &'static str {
        &self.entry().name
    }

    pub fn field_name(self, field: u32) -> &'static str {
        &self.entry().fields[field as usize].0
    }

    pub fn field_index(self, field: &str) -> Option<u32> {
        self.entry()
            .fields
            .iter()
            .position(|(name, _)| name == field)
            .map(|index| index as u32)
    }

    /// The type of a value held in field `field`, `None` for an embedded
    /// record.
    pub fn field_type(self, field: u32) -> Option<super::ProgramType> {
        self.entry().field_types[field as usize]
    }

    /// Where field `field` starts: its fixed byte offset, or its `offsetof`
    /// term.
    pub fn field_offset(self, field: u32) -> LayoutOffset {
        match self.entry().fixed_offsets[field as usize] {
            Some(bytes) => LayoutOffset::Bytes(bytes),
            None => LayoutOffset::Field(self, field),
        }
    }

    /// The end of the fixed prefix, `[0, prefix_end)`: no field at a term
    /// starts before it.
    pub fn prefix_end(self) -> u32 {
        self.entry().prefix_end
    }

    /// The bytes field `field` takes.
    pub fn field_extent(self, field: u32) -> AccessExtent {
        self.entry().fields[field as usize].1
    }

    pub fn field_count(self) -> u32 {
        self.entry().fields.len() as u32
    }

    /// Whether the object is at least one byte: some field takes a known,
    /// nonzero number of bytes. A field of abstract type may take none.
    pub fn size_is_positive(self) -> bool {
        self.entry().prefix_end > 0
            || self
                .entry()
                .fields
                .iter()
                .any(|(_, extent)| matches!(extent, AccessExtent::Bytes(bytes) if *bytes > 0))
    }

    /// `sizeof(name)`.
    pub fn size_term(self) -> MachineTerm {
        MachineTerm::PureFunctionApplication {
            name: self.entry().size_term.to_string(),
            arguments: Vec::new(),
        }
    }

    /// `offsetof(name, field)`.
    pub fn offset_term(self, field: u32) -> MachineTerm {
        MachineTerm::PureFunctionApplication {
            name: self.entry().offset_terms[field as usize].to_string(),
            arguments: Vec::new(),
        }
    }

    /// The last displacement of an address offset when it is a field's,
    /// `rest + offsetof(L, f)`: the offset before it, if any, the layout,
    /// and the field.
    pub(crate) fn field_displacement(
        offset: &super::AddressOffset,
    ) -> Option<(Option<&super::AddressOffset>, Self, u32)> {
        let (rest, last) = match offset {
            super::AddressOffset::Add(rest, last) => (Some(&**rest), &**last),
            other => (None, other),
        };
        let super::AddressOffset::Int64Scaled {
            value,
            byte_width: 1,
            ..
        } = last
        else {
            return None;
        };
        let (layout, Some(field)) = Self::of_term(value.structural_value())? else {
            return None;
        };
        Some((rest, layout, field))
    }

    /// The constant byte displacement of `offset` from an object starting at
    /// `rest` (offset 0 when there is none): `rest` itself is 0, and
    /// `rest + c` or, from a constant start, the constant `c` is `c`.
    pub(crate) fn constant_displacement(
        rest: Option<&super::AddressOffset>,
        offset: &super::AddressOffset,
    ) -> Option<u32> {
        use super::AddressOffset::{Add, Constant};
        let start = rest.unwrap_or(&Constant(0));
        if offset == start {
            return Some(0);
        }
        let displacement = match (start, offset) {
            (Constant(start), Constant(at)) => at.checked_sub(*start)?,
            (_, Add(left, right)) if left.as_ref() == start => match right.as_ref() {
                Constant(at) => *at,
                _ => return None,
            },
            _ => return None,
        };
        u32::try_from(displacement).ok()
    }

    /// Whether an access of `bytes` at displacement `offset` of an object of
    /// this layout lies in its fixed prefix, which no field at a term
    /// reaches.
    pub(crate) fn within_prefix(self, offset: u32, bytes: AccessExtent) -> bool {
        bytes
            .bytes()
            .and_then(|bytes| offset.checked_add(bytes))
            .is_some_and(|end| end <= self.prefix_end())
    }

    /// Whether field `field`, a hole, meets the bytes `[offset, offset +
    /// bytes)` of the fixed prefix.
    pub(crate) fn fixed_field_meets(self, field: u32, offset: u32, bytes: u32) -> bool {
        let entry = self.entry();
        let (Some(start), Some(width)) = (
            entry.fixed_offsets[field as usize],
            entry.fields[field as usize].1.bytes(),
        ) else {
            return false;
        };
        offset < start + width && start < offset.saturating_add(bytes)
    }

    /// Whether an access of `access` bytes at the start of field `field`
    /// stays inside the field.
    pub(crate) fn within_field(self, field: u32, access: AccessExtent) -> bool {
        let extent = self.field_extent(field);
        // No bytes are inside any field.
        access == AccessExtent::Bytes(0)
            || access == extent
            || matches!((access, extent), (AccessExtent::Bytes(a), AccessExtent::Bytes(f)) if a <= f)
    }

    /// The layout and field a term names: `offsetof(L, f)` is `(L, Some(f))`
    /// and `sizeof(L)` is `(L, None)`.
    pub fn of_term(term: &MachineTerm) -> Option<(Self, Option<u32>)> {
        let MachineTerm::PureFunctionApplication { name, arguments } = term else {
            return None;
        };
        if !arguments.is_empty() || !(name.starts_with("offsetof<") || name.starts_with("sizeof<"))
        {
            return None;
        }
        with_registry(|registry| registry.terms.get(name.as_str()).copied())
    }
}

/// The Surface spelling of a size or offset term: `sizeof(T)` for
/// `sizeof<T>`, `offsetof(L, f)` for `offsetof<L, f>`. `None` for any other
/// application, or a layout whose terms carry a collision suffix.
pub fn layout_term_spelling(name: &str, arguments: usize) -> Option<String> {
    if arguments != 0 || name.contains('#') {
        return None;
    }
    if let Some(inner) = name
        .strip_prefix("sizeof<")
        .and_then(|rest| rest.strip_suffix('>'))
    {
        return Some(format!("sizeof({inner})"));
    }
    let inner = name.strip_prefix("offsetof<")?.strip_suffix('>')?;
    let (layout, field) = inner.rsplit_once(", ")?;
    Some(format!("offsetof({layout}, {field})"))
}
