//! Field spellings for constant offsets into struct-typed globals.
//!
//! A memory-history sentence names a cell by its address. An address a
//! constant number of bytes into a struct-typed global otherwise prints as
//! `g+8`; where exactly one scalar field of the global's declared layout
//! occupies exactly the bytes the access covers, the cell is that field,
//! `g.payload.number`. A union whose members share an offset and width, an
//! array member, or an access whose width matches no field keeps the offset.
//!
//! A struct-typed local is named the same way. Its block carries its kernel
//! name (`local:s`, `local:lifetime:2:s`, `local:s#scope1` for a shadowing
//! declaration), and the table is keyed by that name from the declarations
//! themselves, which carry the layout. Two declarations in sibling scopes
//! can share a kernel name; when their layouts differ, the name keeps the
//! offset. A global's block is its unique kernel name.
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
    globals: std::collections::HashMap<String, (String, u32, Vec<ObjectField>)>,
    locals: std::collections::HashMap<String, Option<(String, u32, Vec<ObjectField>)>>,
    /// The function's struct layouts by name, for the struct a pointer field
    /// points at.
    structs: syntax::DeclarationMap<syntax::C0StructLayout>,
}

thread_local! {
    static AMBIENT_OBJECT_FIELDS: std::cell::RefCell<Option<std::rc::Rc<ObjectFields>>> =
        const { std::cell::RefCell::new(None) };
}

/// Starts naming the struct-typed globals `function` can reach and the
/// struct-typed locals it declares.
pub(crate) fn enter_ambient_object_fields(function: &syntax::C0Function) {
    let mut objects = ObjectFields {
        structs: function.structs().clone(),
        ..ObjectFields::default()
    };
    for aggregate in function.global_aggregates().values() {
        let block = if PointerBlock::is_global_name(aggregate.kernel_name()) {
            aggregate.kernel_name().to_string()
        } else {
            format!("global:{}", aggregate.kernel_name())
        };
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
        if let syntax::C0Statement::DeclareStructValue { name, layout, .. } = statement {
            let mut fields = Vec::new();
            collect_struct_fields(function, layout, "", 0, &mut fields, 0);
            // A shadowing declaration's kernel name is `s#scope1`; the
            // reader wrote `s`.
            let source = name.split('#').next().unwrap_or(name).to_string();
            let declared = (source, layout.size_bytes(), fields);
            objects
                .locals
                .entry(name.clone())
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
    block: &str,
) -> Option<&'a (String, u32, Vec<ObjectField>)> {
    if PointerBlock::is_local_name(block) {
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
        return objects.locals.get(name)?.as_ref();
    }
    objects.globals.get(block)
}

pub(crate) fn clear_ambient_object_fields() {
    AMBIENT_OBJECT_FIELDS.with(|slot| *slot.borrow_mut() = None);
}

/// How deep embedded structs and unions are followed.
const MAX_NESTING: usize = 8;

/// A scalar field's width, when its declared type is one: arrays, embedded
/// aggregates and `long double` are not single cells a width can match.
fn scalar_width(c_type: C0Type, byte_width: u32, long_double: bool) -> Option<u32> {
    let width = match c_type {
        C0Type::Bool | C0Type::Char(_) | C0Type::Int8 | C0Type::UInt8 => 1,
        C0Type::Int16 | C0Type::UInt16 => 2,
        C0Type::Int32 | C0Type::UInt32 | C0Type::Float32 => 4,
        C0Type::Int64(_) | C0Type::UInt64(_) | C0Type::Float64 => 8,
        _ if c_type.is_pointer() => 8,
        _ => return None,
    };
    (!long_double && width == byte_width).then_some(width)
}

fn collect_struct_fields(
    function: &syntax::C0Function,
    layout: &syntax::C0StructLayout,
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
        } else if let Some(width) =
            scalar_width(field.c_type(), field.byte_width(), field.is_long_double())
        {
            out.push(ObjectField {
                offset,
                width,
                path,
            });
        }
    }
}

fn collect_union_fields(
    function: &syntax::C0Function,
    layout: &syntax::C0UnionLayout,
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
        } else if let Some(width) =
            scalar_width(field.c_type(), field.byte_width(), field.is_long_double())
        {
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
pub(super) fn ambient_struct_layout(name: &str) -> Option<syntax::C0StructLayout> {
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        slot.borrow()
            .as_ref()
            .and_then(|objects| objects.structs.get(name).cloned())
    })
}

pub(super) fn object_field_spelling(block: &str, offset: u32, width: u32) -> Option<String> {
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
pub(super) fn object_range_spelling(range: &CMemoryRange) -> Option<String> {
    let PointerBlock::Concrete(block) = &range.base().block else {
        return None;
    };
    let PointerOffsetTerm::Constant(offset) = &range.base().offset else {
        return None;
    };
    let offset = u64::try_from(*offset).ok()?;
    let width = u64::from(range.element_width());
    let start = offset.checked_add(u64::from(range.constant_start()?).checked_mul(width)?)?;
    let end = offset.checked_add(u64::from(range.constant_end()?).checked_mul(width)?)?;
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        let slot = slot.borrow();
        let (name, size, _) = declared_object(slot.as_ref()?, block)?;
        (start == 0 && end == u64::from(*size)).then(|| name.clone())
    })
}
