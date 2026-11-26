//! Field spellings for constant offsets into struct-typed globals.
//!
//! A memory-history sentence names a cell by its address. An address a
//! constant number of bytes into a struct-typed global otherwise prints as
//! `g+8`; where exactly one scalar field of the global's declared layout
//! occupies exactly the bytes the access covers, the cell is that field,
//! `g.payload.number`. A union whose members share an offset and width, an
//! array member, or an access whose width matches no field keeps the offset.
//!
//! A struct-typed C local is indexed by its typed declaration identity. Every
//! lifetime and call-frame instance of that declaration uses the same layout.
//! Non-C legacy bindings keep their named storage keys.
//!
//! Diagnostics only: nothing a check decides reads these spellings. The table
//! is built when a function's verification starts, from its declarations.

use super::*;

/// One scalar field of an object: its byte offset inside the object, its
/// width, and its member path (`payload.number`).
struct ObjectField {
    offset: u32,
    width: u32,
    path: String,
}

/// The source name, size and scalar fields of each struct-typed global, by
/// the kernel block that holds it, and of each struct-typed local, by its
/// kernel name (`None` when declarations sharing the name differ in layout).
#[derive(Default)]
struct ObjectFields {
    globals: std::collections::HashMap<AddressBase, (String, u32, Vec<ObjectField>)>,
    locals: std::collections::HashMap<
        crate::kernel::BindingName,
        Option<(String, u32, Vec<ObjectField>)>,
    >,
    /// The function's struct layouts by name, for the struct a pointer field
    /// points at.
    structs: syntax::DeclarationMap<crate::languages::interface::RecordLayout>,
    /// The struct each struct-pointer local points to, by its kernel name.
    pointer_locals: std::collections::BTreeMap<crate::kernel::BindingName, String>,
}

thread_local! {
    static AMBIENT_OBJECT_FIELDS: std::cell::RefCell<Option<std::rc::Rc<ObjectFields>>> =
        const { std::cell::RefCell::new(None) };
}

/// Starts naming the struct-typed globals `function` can reach and the
/// struct-typed locals it declares.
pub(crate) fn enter_ambient_object_fields(
    function: &crate::languages::interface::ImportedFunction,
) {
    let mut objects = ObjectFields {
        structs: function.structs().clone(),
        pointer_locals: function.local_struct_pointers().clone(),
        ..ObjectFields::default()
    };
    for aggregate in function.global_aggregates().values() {
        let block = crate::kernel::SymbolicMemory::global_pointer(aggregate.kernel_name())
            .base
            .clone();
        let mut fields = Vec::new();
        collect_struct_fields(function, aggregate.layout(), "", 0, &mut fields, 0);
        objects.globals.insert(
            block,
            (
                aggregate.name().to_string(),
                aggregate.layout().size_bytes(),
                fields,
            ),
        );
    }
    let mut pending = vec![function.body()];
    while let Some(statement) = pending.pop() {
        if let syntax::CStatement::DeclareStructValue { name, layout, .. } = statement {
            let mut fields = Vec::new();
            collect_struct_fields(function, layout, "", 0, &mut fields, 0);
            let source = name.source_name().to_owned();
            let declared = (source, layout.size_bytes(), fields);
            objects
                .locals
                .entry(name.binding().clone())
                .and_modify(|existing| {
                    if existing.as_ref().is_some_and(|existing| {
                        existing.1 != declared.1 || !same_fields(&existing.2, &declared.2)
                    }) {
                        *existing = None;
                    }
                })
                .or_insert(Some(declared));
        }
        let mut expressions = Vec::new();
        crate::languages::c::address_taken::child_statements(
            statement,
            &mut expressions,
            &mut pending,
        );
    }
    AMBIENT_OBJECT_FIELDS.with(|slot| *slot.borrow_mut() = Some(std::rc::Rc::new(objects)));
}

fn same_fields(left: &[ObjectField], right: &[ObjectField]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            left.offset == right.offset && left.width == right.width && left.path == right.path
        })
}

/// The declared object in `block`: a global by its block, a local by the
/// kernel name its block ends with.
fn declared_object<'a>(
    objects: &'a ObjectFields,
    block: &AddressBase,
) -> Option<&'a (String, u32, Vec<ObjectField>)> {
    if let Some(object) = objects.globals.get(block) {
        return Some(object);
    }
    if let AddressBase::AutomaticLocal { binding, .. } = block {
        return objects.locals.get(&binding.clone().into())?.as_ref();
    }
    let AddressBase::Concrete(block) = block else {
        return None;
    };
    if AddressBase::is_local_name(block) {
        // This function's own automatic objects only: a callee's frame
        // (`local:frame:3:s`) can reuse a name for another type.
        let rest = block.strip_prefix("local:")?;
        let name = match rest.strip_prefix("lifetime:") {
            Some(generation) => generation.split_once(':')?.1,
            None => rest,
        };
        if name.contains(':') {
            return None;
        }
        return objects.locals.get(&name.into())?.as_ref();
    }
    None
}

pub(crate) fn clear_ambient_object_fields() {
    AMBIENT_OBJECT_FIELDS.with(|slot| *slot.borrow_mut() = None);
}

/// How deep embedded structs and unions are followed.
const MAX_NESTING: usize = 8;

/// A scalar field's width, when its declared type is one: arrays, embedded
/// aggregates and `long double` are not single cells a width can match.
fn scalar_width(interface_type: InterfaceType, byte_width: u32, long_double: bool) -> Option<u32> {
    let width = match interface_type {
        InterfaceType::Bool
        | InterfaceType::Char(_)
        | InterfaceType::Int8
        | InterfaceType::UInt8 => 1,
        InterfaceType::Int16 | InterfaceType::UInt16 => 2,
        InterfaceType::Int32 | InterfaceType::UInt32 | InterfaceType::Float32 => 4,
        InterfaceType::Int64(_) | InterfaceType::UInt64(_) | InterfaceType::Float64 => 8,
        _ if interface_type.is_pointer() => 8,
        _ => return None,
    };
    (!long_double && width == byte_width).then_some(width)
}

fn collect_struct_fields(
    function: &crate::languages::interface::ImportedFunction,
    layout: &crate::languages::interface::RecordLayout,
    prefix: &str,
    base: u32,
    out: &mut Vec<ObjectField>,
    depth: usize,
) {
    if depth > MAX_NESTING {
        return;
    }
    for (name, field) in layout.fields() {
        let path = format!("{prefix}{name}");
        let Some(offset) = base.checked_add(field.offset_bytes()) else {
            continue;
        };
        if field.array_shape().is_some() || field.array_element_width().is_some() {
            continue;
        }
        if let Some(nested) = field.struct_name() {
            if let Some(nested) = function.structs().get(nested) {
                collect_struct_fields(
                    function,
                    nested,
                    &format!("{path}."),
                    offset,
                    out,
                    depth + 1,
                );
            }
        } else if let Some(union) = field.union_name() {
            if let Some(union) = function.unions().get(union) {
                collect_union_fields(function, union, &format!("{path}."), offset, out, depth + 1);
            }
        } else if let Some(width) = scalar_width(
            field.interface_type(),
            field.byte_width(),
            field.is_long_double(),
        ) {
            out.push(ObjectField {
                offset,
                width,
                path,
            });
        }
    }
}

fn collect_union_fields(
    function: &crate::languages::interface::ImportedFunction,
    layout: &syntax::CUnionLayout,
    prefix: &str,
    base: u32,
    out: &mut Vec<ObjectField>,
    depth: usize,
) {
    if depth > MAX_NESTING {
        return;
    }
    for (name, field) in layout.fields() {
        let path = format!("{prefix}{name}");
        let Some(offset) = base.checked_add(field.offset_bytes()) else {
            continue;
        };
        if field.array_shape().is_some() {
            continue;
        }
        if let Some(nested) = field.struct_name() {
            if let Some(nested) = function.structs().get(nested) {
                collect_struct_fields(
                    function,
                    nested,
                    &format!("{path}."),
                    offset,
                    out,
                    depth + 1,
                );
            }
        } else if let Some(width) = scalar_width(
            field.interface_type(),
            field.byte_width(),
            field.is_long_double(),
        ) {
            out.push(ObjectField {
                offset,
                width,
                path,
            });
        }
    }
}

/// The field spelling of the `width` bytes at `offset` into the struct
/// object in `block`, when exactly one scalar field occupies exactly those
/// bytes.
/// The layout of the struct named `name` in the function being described.
pub(super) fn ambient_struct_layout(
    name: &str,
) -> Option<crate::languages::interface::RecordLayout> {
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        slot.borrow()
            .as_ref()
            .and_then(|objects| objects.structs.get(name).cloned())
    })
}

/// The struct a struct-pointer local of the function being described points
/// to, by its declared name and layout. A naming table holds a local by its
/// source spelling; declarations sharing that spelling must agree.
pub(super) fn ambient_local_struct_pointee(
    spelling: &str,
) -> Option<(String, crate::languages::interface::RecordLayout)> {
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        let objects = slot.borrow();
        let objects = objects.as_ref()?;
        let mut pointees = objects
            .pointer_locals
            .iter()
            .filter(|(local, _)| local.source_name() == spelling)
            .map(|(_, struct_name)| struct_name);
        let struct_name = pointees.next()?;
        if pointees.any(|other| other != struct_name) {
            return None;
        }
        Some((
            struct_name.clone(),
            objects.structs.get(struct_name)?.clone(),
        ))
    })
}

pub(super) fn object_field_surface(block: &AddressBase, offset: u32, width: u32) -> Option<String> {
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        let slot = slot.borrow();
        let (name, _, fields) = declared_object(slot.as_ref()?, block)?;
        let mut matching = fields
            .iter()
            .filter(|field| field.offset == offset && field.width == width);
        let field = matching.next()?;
        matching
            .next()
            .is_none()
            .then(|| format!("{name}.{}", field.path))
    })
}

/// The declared object's name when a range covers exactly its complete ABI storage.
pub(super) fn object_range_spelling(range: &MemoryRange) -> Option<String> {
    let block = &range.base().base;
    let OffsetView::Constant(offset) = range.base().offset.view() else {
        return None;
    };
    let offset = u64::try_from(offset).ok()?;
    let width = u64::from(range.element_width());
    let start = offset.checked_add(u64::from(range.constant_start()?).checked_mul(width)?)?;
    let end = offset.checked_add(u64::from(range.constant_end()?).checked_mul(width)?)?;
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        let slot = slot.borrow();
        let (name, size, _) = declared_object(slot.as_ref()?, block)?;
        (start == 0 && end == u64::from(*size)).then(|| name.clone())
    })
}
