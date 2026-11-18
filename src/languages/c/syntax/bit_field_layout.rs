//! Layout of nonzero-width int bit-fields on the x86-64 System V target.
//! Type promotion and signedness are separate from where the bits are placed.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IntBitField {
    start_bit: u64,
    width: u8,
}

impl IntBitField {
    /// Select the next position after the preceding member. An int bit-field
    /// must fit inside one naturally aligned 32-bit allocation unit. The next
    /// ordinary member can use any bytes the field did not occupy, subject
    /// to that member's own alignment.
    pub(crate) fn place(cursor: u64, width: u8) -> Option<Self> {
        let width_bits = u64::from(width);
        if !(1..=32).contains(&width) {
            return None;
        }
        let start_bit = if cursor % 32 + width_bits <= 32 {
            cursor
        } else {
            cursor.checked_add(32 - cursor % 32)?
        };
        start_bit.checked_add(width_bits)?;
        Some(Self { start_bit, width })
    }

    pub(super) fn start_bit(self) -> u64 {
        self.start_bit
    }

    /// An unnamed zero-width int member advances placement to a unit boundary.
    pub(super) fn next_word(cursor: u64) -> Option<u64> {
        cursor.div_ceil(32).checked_mul(32)
    }

    pub(super) fn shift_in_word(self) -> u32 {
        (self.start_bit % 32) as u32
    }

    pub(super) fn width(self) -> u8 {
        self.width
    }

    pub(crate) fn end_bit(self) -> u64 {
        self.start_bit + u64::from(self.width)
    }

    /// Iterate just the intersected bytes. Masks use x86-64's least
    /// significant bit numbering within each byte.
    pub(crate) fn byte_masks(self) -> impl Iterator<Item = (u64, u8)> {
        let end = self.end_bit();
        (self.start_bit / 8..end.div_ceil(8)).map(move |offset| {
            let byte_start = offset * 8;
            let low = self.start_bit.saturating_sub(byte_start);
            let high = (end - byte_start).min(8);
            let mask = (((1u16 << high) - 1) ^ ((1u16 << low) - 1)) as u8;
            (offset, mask)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sysv_int_fields_share_bytes_and_restart_at_unit_boundaries() {
        let ready = IntBitField::place(0, 1).unwrap();
        let busy = IntBitField::place(ready.end_bit(), 1).unwrap();
        assert_eq!(ready.byte_masks().collect::<Vec<_>>(), [(0, 1)]);
        assert_eq!(busy.byte_masks().collect::<Vec<_>>(), [(0, 2)]);

        // Corresponds to a char prefix, a 17-bit field, then a 9-bit field.
        let first = IntBitField::place(8, 17).unwrap();
        let second = IntBitField::place(first.end_bit(), 9).unwrap();
        assert_eq!(
            first.byte_masks().collect::<Vec<_>>(),
            [(1, 255), (2, 255), (3, 1)]
        );
        assert_eq!(second.byte_masks().collect::<Vec<_>>(), [(4, 255), (5, 1)]);
        assert_eq!(second.end_bit().div_ceil(8), 6);
    }

    #[test]
    fn far_offsets_and_invalid_widths_do_not_wrap() {
        let offset = u64::from(u32::MAX - 3);
        let field = IntBitField::place(offset * 8, 32).unwrap();
        assert_eq!(field.byte_masks().count(), 4);
        assert_eq!(field.byte_masks().last(), Some((u64::from(u32::MAX), 255)));
        assert_eq!(IntBitField::place(u64::MAX, 1), None);
        assert_eq!(IntBitField::place(0, 0), None);
        assert_eq!(IntBitField::place(0, 33), None);
    }
}
