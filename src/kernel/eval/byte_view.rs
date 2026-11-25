//! The byte view of integer cells.
//!
//! SymbolicMemory keeps typed cells, not bytes. A one-byte C access that lands inside
//! a wider integer cell, rather than on a cell of its own, still has a defined
//! meaning once the target's byte order is known: under little-endian order,
//! byte `k` of an integer object holds bits `8k .. 8k + 8` of its value. This
//! module is the only place that meaning is written down.
//!
//! The view is deliberately narrow:
//!
//! - only a C execution access of width one, at a constant offset, inside an
//!   integer cell at a constant offset of the same block;
//! - only under [`ByteOrder::Little`] installed from the execution
//!   environment; with no installed order, or under `Big`, there is no view;
//! - never for a pointer, float, or `_Bool` cell. A pointer's bytes are
//!   opaque, which is what keeps a pointer rebuilt from bytes refused.
//!
//! The containing cell is found with a bounded range query over the at most
//! seven constant offsets below the access in its own block, so the lookup
//! does work independent of every other cell in memory.

use super::*;

/// The widest integer cell, in bytes. A containing cell starts at most this
/// many bytes minus one below the accessed byte.
const WIDEST_INTEGER_CELL_BYTES: i64 = 8;

/// Recover a retained byte without treating partial values as byte cells.
pub(in crate::kernel) fn known_integer_byte(
    memory: &SymbolicMemory,
    pointer: &Address,
    byte_order: Option<ByteOrder>,
) -> Option<OldMachineTerm> {
    if let Some(value) = memory.cells.get(pointer) {
        match value {
            ProgramValue::UInt8(bits) => return Some(bits.clone()),
            ProgramValue::Int8(bits) => {
                return Some(OldMachineTerm::machine_integer_cast(
                    MachineIntegerType::Int8,
                    MachineIntegerType::UInt8,
                    bits.clone(),
                ));
            }
            _ => {}
        }
    }
    let cell = containing_integer_cell(memory, pointer, byte_order)?;
    integer_cell_byte(&cell.value, cell.byte)
}

pub(in crate::kernel) fn mask_byte(value: OldMachineTerm, mask: u8) -> OldMachineTerm {
    use MachineIntegerType::{UInt8, UInt32};
    if mask == u8::MAX {
        return value;
    }
    let word = OldMachineTerm::machine_integer_cast(UInt8, UInt32, value);
    let bits =
        OldMachineTerm::bitwise_and_at(UInt32, word, OldMachineTerm::constant(u32::from(mask)));
    OldMachineTerm::machine_integer_cast(UInt32, UInt8, bits)
}

pub(super) fn merge_byte_bits(left: OldMachineTerm, right: OldMachineTerm) -> OldMachineTerm {
    use MachineIntegerType::{UInt8, UInt32};
    let left = OldMachineTerm::machine_integer_cast(UInt8, UInt32, left);
    let right = OldMachineTerm::machine_integer_cast(UInt8, UInt32, right);
    let word = OldMachineTerm::bitwise_or_at(UInt32, left, right);
    OldMachineTerm::machine_integer_cast(UInt32, UInt8, word)
}

/// A completed byte output for a declared uint32 relates its word and bytes.
/// The equation names only the selected output state; initialization and
/// authority come from the checked output transfer, not from this equation.
pub(in crate::kernel) fn declared_uint32_read_representation(
    point: &ProgramPoint,
    pointer: &Address,
    byte_order: Option<ByteOrder>,
) -> Option<Proposition> {
    if byte_order != Some(ByteOrder::Little) || pointer.offset.as_const() != Some(0) {
        return None;
    }
    crate::instrumentation::record_deterministic_work(1);
    let memory = point.memory();
    let declaration = memory.blocks.get(&pointer.base)?;
    if declaration.declared_scalar_type != Some(ProgramType::UInt32)
        || declaration.size().as_const() != Some(4)
        || memory.is_ended_local_address(pointer)
    {
        return None;
    }
    let value = super::memory_loads::canonical_cell_load(point, pointer, ProgramType::UInt32);
    let mut assembled = OldMachineTerm::constant(0);
    for byte in 0..4 {
        crate::instrumentation::record_deterministic_work(1);
        let read = super::memory_loads::canonical_cell_load(
            point,
            &pointer.offset_by_bytes(byte),
            ProgramType::UInt8,
        );
        let bits = byte_word(&ProgramValue::UInt8(read))?;
        assembled = OldMachineTerm::bitwise_or(
            assembled,
            OldMachineTerm::unsigned_shift_left(bits, OldMachineTerm::constant(8 * byte)),
        );
    }
    Some(Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: Box::new(value),
            right: Box::new(assembled),
        },
        true,
    ))
}

/// Assemble the logical read of one declared word from complete indexed
/// byte writes. Its term is the ordinary Click byte expression, with each
/// byte naming its own version. The access itself has its own obligations.
pub(in crate::kernel) fn indexed_uint32_byte_read(
    point: &ProgramPoint,
    pointer: &Address,
    byte_order: Option<ByteOrder>,
) -> Option<(ProgramValue, ExecutionFacts)> {
    if byte_order != Some(ByteOrder::Little)
        || pointer.offset != OldAddressOffset::Constant(0)
        || point.memory().is_ended_local_address(pointer)
    {
        return None;
    }
    // This is the original declared storage, not a cast of a byte buffer.
    let declaration = point.memory().blocks.get(&pointer.base)?;
    if declaration.declared_scalar_type != Some(ProgramType::UInt32)
        || declaration.size().as_const() != Some(4)
    {
        return None;
    }
    let mut facts = ExecutionFacts::new();
    let mut packed = OldMachineTerm::constant(0);
    for byte in 0..4 {
        crate::instrumentation::record_deterministic_work(1);
        let address = pointer.offset_by_bytes(byte);
        let version = point.indexed_integer_version(&address, LoadKind::UInt8)?;
        let path = super::memory_loads::evaluate_indexed_read(
            version,
            point,
            address,
            ProgramType::UInt8,
            facts,
            Vec::new(),
        );
        let ExpressionOutcome::Value(value) = path.outcome else {
            unreachable!("indexed byte read");
        };
        facts = path.facts;
        let term = byte_word(&value)?;
        let shifted = OldMachineTerm::unsigned_shift_left(term, OldMachineTerm::constant(8 * byte));
        packed = OldMachineTerm::bitwise_or(packed, shifted);
    }
    Some((ProgramValue::UInt32(packed), facts))
}

/// Completes an automatic uint32 object's representation when this character
/// store supplies its last missing byte. Its declaration, not the requested
/// load type or the allocation's size, selects the object being initialized.
/// Four exact initialized character cells suffice; partial representations,
/// untyped storage, other scalar kinds and other byte orders do not.
///
/// This is the same checked store normalization as updating a byte of an
/// existing integer cell: the resulting typed cell replaces the byte cells,
/// and the ordinary store transition invalidates overlapping cached values.
pub(in crate::kernel) fn assemble_declared_uint32_after_byte_store(
    memory: &SymbolicMemory,
    pointer: &Address,
    stored: &ProgramValue,
    byte_order: Option<ByteOrder>,
) -> Option<(Address, ProgramValue)> {
    if byte_order != Some(ByteOrder::Little) {
        return None;
    }
    let offset = pointer.offset.as_const()?;
    if !(0..4).contains(&offset) {
        return None;
    }
    crate::instrumentation::record_deterministic_work(1);
    let declaration = memory.blocks.get(&pointer.base)?;
    if declaration.declared_scalar_type != Some(ProgramType::UInt32)
        || declaration.size().as_const() != Some(4)
        || memory.is_ended_local_address(pointer)
    {
        return None;
    }
    let as_byte = byte_word;
    let incoming = as_byte(stored)?;
    let start = Address {
        base: pointer.base.clone(),
        offset: OldAddressOffset::Constant(0),
    };
    let mut assembled = OldMachineTerm::constant(0);
    for byte in 0..4 {
        crate::instrumentation::record_deterministic_work(1);
        let bits = if byte == offset {
            incoming.clone()
        } else {
            as_byte(&memory.cells.get(&start.offset_by_bytes(byte as u32))?)?
        };
        assembled = OldMachineTerm::bitwise_or(
            assembled,
            OldMachineTerm::unsigned_shift_left(bits, OldMachineTerm::constant(8 * byte as u32)),
        );
    }
    Some((start, ProgramValue::UInt32(assembled)))
}

/// The 32-bit word of a stored byte, `0..=255`: the zero extension of its
/// eight bits, `uint8` read directly and `int8` through its conversion to
/// `uint8`. `None` for a value that is not a byte.
fn byte_word(value: &ProgramValue) -> Option<OldMachineTerm> {
    use crate::kernel::MachineIntegerType as Ty;
    let byte = match value {
        ProgramValue::UInt8(bits) => bits.clone(),
        ProgramValue::Int8(bits) => {
            OldMachineTerm::machine_integer_cast(Ty::Int8, Ty::UInt8, bits.clone())
        }
        _ => return None,
    };
    Some(OldMachineTerm::machine_integer_cast(
        Ty::UInt8,
        Ty::Int32,
        byte,
    ))
}

/// An integer cell that contains a one-byte access without starting at it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ContainingIntegerCell {
    /// The cell's own address, `(block, const o')`.
    pub(in crate::kernel) pointer: Address,
    /// The cell's value, an integer variant wider than one byte.
    pub(in crate::kernel) value: ProgramValue,
    /// Which byte of the cell's representation the access names, `o - o'`.
    pub(in crate::kernel) byte: u32,
}

/// The byte width of an integer cell, or `None` for a cell with no byte view.
fn integer_cell_width(value: &ProgramValue) -> Option<u32> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int8(_) | ProgramValue::UInt8(_) => Some(1),
        ProgramValue::Int16(_) | ProgramValue::UInt16(_) => Some(2),
        ProgramValue::Int32(_) | ProgramValue::UInt32(_) => Some(4),
        ProgramValue::Int64(_) | ProgramValue::UInt64(_) => Some(8),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::Bool(_)
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_)
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_) => None,
    }
}

/// The integer cell that contains the byte at `pointer`, when the byte order
/// gives it a byte view.
///
/// The containing cell starts at `(block, const o')` with
/// `o' <= o < o' + w` and `w > 1`. Returns `None` for any order other than an
/// installed little-endian one, a symbolic offset, a one-byte cell at
/// `pointer` (that cell, not a byte view, is what the access names), no
/// overlapping cell, or an overlapping cell with no byte view (pointer,
/// float, `_Bool`).
pub(in crate::kernel) fn containing_integer_cell(
    memory: &SymbolicMemory,
    pointer: &Address,
    byte_order: Option<ByteOrder>,
) -> Option<ContainingIntegerCell> {
    if byte_order != Some(ByteOrder::Little) {
        return None;
    }
    let OldAddressOffset::Constant(offset) = pointer.offset else {
        return None;
    };
    crate::instrumentation::record_deterministic_work(1);
    // A cell at the access's own address is the containing cell when it is
    // a wider integer (byte 0). A one-byte cell there is the access's own
    // cell, which the exact rules read and write; a cell with no byte view
    // is refused.
    if let Some(value) = memory.cells.get(pointer) {
        return (integer_cell_width(&value)? > 1).then(|| ContainingIntegerCell {
            pointer: pointer.clone(),
            value: value.clone(),
            byte: 0,
        });
    }
    let lowest = offset.checked_sub(WIDEST_INTEGER_CELL_BYTES - 1)?;
    // There are at most seven possible starts. Exact lookups use the
    // concrete and run indexes without materializing the logical cell map.
    for cell_offset in (lowest..offset).rev() {
        let cell_pointer = Address {
            base: pointer.base.clone(),
            offset: OldAddressOffset::Constant(cell_offset),
        };
        crate::instrumentation::record_deterministic_work(1);
        let Some(value) = memory.cells.get(&cell_pointer) else {
            continue;
        };
        let width = integer_cell_width(&value);
        let reach =
            width.unwrap_or_else(|| crate::kernel::reasoning::cell_access_byte_width(&value));
        let byte = (offset - cell_offset) as u32;
        if reach <= byte {
            continue;
        }
        // The nearest overlapping cell decides. A cell without a byte view
        // refuses the access rather than letting a farther cell answer.
        width?;
        return Some(ContainingIntegerCell {
            pointer: cell_pointer,
            value,
            byte,
        });
    }
    None
}

/// Byte `byte` of an integer cell's little-endian representation, as the
/// `unsigned char` it is: the conversion to `uint8` of `v >> 8k`, a native
/// 8-bit term. A 16-bit value is read through its 32-bit widening, whose
/// low sixteen bits are its representation whatever its signedness.
pub(in crate::kernel) fn integer_cell_byte(
    value: &ProgramValue,
    byte: u32,
) -> Option<OldMachineTerm> {
    use crate::kernel::MachineIntegerType as Ty;
    let value = value.numeric_value();
    let width = integer_cell_width(value)?;
    if byte >= width {
        return None;
    }
    let shift = 8 * byte;
    let word = |term: OldMachineTerm| {
        let shifted = if shift == 0 {
            term
        } else {
            OldMachineTerm::logical_shift_right(term, OldMachineTerm::constant(shift))
        };
        OldMachineTerm::machine_integer_cast(Ty::UInt32, Ty::UInt8, shifted)
    };
    Some(match value {
        ProgramValue::Int16(term) | ProgramValue::UInt16(term) => {
            word(OldMachineTerm::machine_integer_cast(
                Ty::from_program_type(value.program_type())?,
                Ty::UInt32,
                term.clone(),
            ))
        }
        ProgramValue::Int32(term) | ProgramValue::UInt32(term) => word(term.clone()),
        ProgramValue::Int64(term) | ProgramValue::UInt64(term) => {
            let bits = match value {
                ProgramValue::Int64(_) => OldMachineTerm::uint64_from_int64(term.clone()),
                _ => term.clone(),
            };
            let shifted = if shift == 0 {
                bits
            } else {
                OldMachineTerm::uint64_logical_shift_right(
                    bits,
                    OldMachineTerm::uint64_constant(u64::from(shift)),
                )
            };
            OldMachineTerm::machine_integer_cast(Ty::UInt64, Ty::UInt8, shifted)
        }
        _ => return None,
    })
}

/// The value a one-byte load of `value_type` reads from byte `byte` of an
/// integer cell. An `unsigned char` reads the byte; a `signed char` reads its
/// two's-complement reading, which is decided here only for a constant
/// byte; a symbolic signed byte view is refused, as before native bytes.
pub(in crate::kernel) fn byte_view_load_value(
    cell: &ContainingIntegerCell,
    value_type: ProgramType,
) -> Option<ProgramValue> {
    use crate::kernel::MachineIntegerType as Ty;
    let byte = integer_cell_byte(&cell.value, cell.byte)?;
    match value_type {
        ProgramType::UInt8 => Some(ProgramValue::UInt8(byte)),
        ProgramType::Int8 => Ty::UInt8.constant_from_term(&byte).map(|_| {
            ProgramValue::Int8(OldMachineTerm::machine_integer_cast(
                Ty::UInt8,
                Ty::Int8,
                byte,
            ))
        }),
        _ => None,
    }
}

/// The integer cell `cell` after a one-byte store of `stored` at its byte
/// `cell.byte`, under little-endian order:
/// `(v & !(0xFF << 8k)) | (zext(b) << 8k)`, in the cell's own variant.
///
/// An `int16_t` or `int64_t` cell is updated only when both the cell and the
/// byte are constants: its term would otherwise need a sign extension (16-bit)
/// or a signed shift into the sign bit (64-bit) that no term operation states.
/// `None` leaves the store to forget the cell, as it did before this view.
pub(in crate::kernel) fn integer_cell_with_byte(
    cell: &ContainingIntegerCell,
    stored: &ProgramValue,
) -> Option<ProgramValue> {
    let width = integer_cell_width(&cell.value)?;
    if width <= 1 || cell.byte >= width {
        return None;
    }
    let byte = byte_word(stored)?;
    let shift = 8 * cell.byte;
    // `byte < width <= 8`, so the 64-bit shift is in range; the 32-bit mask
    // is only used by cells of at most four bytes, where it is too.
    let mask32 = !0xFFu32.checked_shl(shift).unwrap_or(0);
    let mask64 = !(0xFFu64 << shift);
    let update32 = |term: &OldMachineTerm| {
        OldMachineTerm::bitwise_or(
            OldMachineTerm::bitwise_and(term.clone(), OldMachineTerm::constant(mask32)),
            OldMachineTerm::unsigned_shift_left(byte.clone(), OldMachineTerm::constant(shift)),
        )
    };
    use crate::kernel::MachineIntegerType as Ty;
    Some(match cell.value.numeric_value() {
        // A 16-bit cell is updated in its 32-bit widening and converted back.
        ProgramValue::UInt16(term) => ProgramValue::UInt16(OldMachineTerm::machine_integer_cast(
            Ty::UInt32,
            Ty::UInt16,
            update32(&OldMachineTerm::machine_integer_cast(
                Ty::UInt16,
                Ty::UInt32,
                term.clone(),
            )),
        )),
        ProgramValue::Int32(term) => ProgramValue::Int32(update32(term)),
        ProgramValue::UInt32(term) => ProgramValue::UInt32(update32(term)),
        ProgramValue::UInt64(term) => ProgramValue::UInt64(OldMachineTerm::uint64_bitwise_or(
            OldMachineTerm::uint64_bitwise_and(
                term.clone(),
                OldMachineTerm::uint64_constant(mask64),
            ),
            OldMachineTerm::uint64_shift_left(
                OldMachineTerm::uint64_from_32(byte),
                OldMachineTerm::uint64_constant(u64::from(shift)),
            ),
        )),
        ProgramValue::Int16(term) => {
            let value = Ty::Int16.constant_from_term(term)?.bits() as u32;
            let byte = byte.as_const()?;
            let bits = (value & 0xFFFF & mask32) | ((byte & 0xFF) << shift);
            crate::kernel::int16(bits as u16 as i16 as i32 as u32)
        }
        ProgramValue::Int64(term) => {
            let (value, byte) = (term.int64_as_const()?, byte.as_const()?);
            let bits = (value as u64 & mask64) | (u64::from(byte & 0xFF) << shift);
            ProgramValue::Int64(OldMachineTerm::int64_constant(bits as i64))
        }
        _ => return None,
    })
}
