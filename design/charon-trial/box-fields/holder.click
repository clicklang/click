verifying "holder.rs";

// A struct's `Option<Box<Cell>>` field is the box's address, or null. Owning
// the field holds its value's type resource,
// `Option<Box<box_fields::Cell>>(self.slot)`: the box, when it is `Some`.
impl box_fields::Holder {
    // `self.slot.take()` moves the box out of the field and leaves `None`;
    // the box is freed when the match's binding drops.
    fn read(&mut self) -> u32 {
        owns self.slot;
        ensures old(self.slot) != 0 implies result == old(self.slot.value);
        ensures old(self.slot) == 0 implies result == 0u32;
        ensures self.slot == 0;
    }

    // Assigning the field drops its old value in place, which the `take`
    // left `None`; the taken box drops at scope end.
    fn put(&mut self, x: u32) {
        owns self.slot;
        ensures self.slot != 0;
        ensures self.slot.value == x;
    }
}
