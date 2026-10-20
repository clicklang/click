verifying "holder.rs";

// A struct's `Option<Box<Cell>>` field is the box's address, or null: the
// resource owns the allocation and the cell when it is `Some`.
resource slot(p: *mut box_fields::Cell) {
    field value: Option<u32>;
    match value {
        Option::None => { fact p == 0; },
        Option::Some(v) => {
            owns allocation(p, sizeof(box_fields::Cell));
            owns *p;
            fact p != 0;
            fact p.value == v;
        },
    }
}

impl box_fields::Holder {
    // `self.slot.take()` moves the box out of the field and leaves `None`;
    // the box is freed when the match's binding drops.
    fn read(&mut self) -> u32 {
        owns self.slot;
        consumes before: slot(self.slot);
        ensures result == (match old(before.value) { Option::Some(v) => v, Option::None => 0u32 });
        ensures self.slot == 0;
    } by {
        match before.value {
            Option::None => {
                let {} = unfold(before);
                execute();
                simp();
            }
            Option::Some(v) => {
                let {} = unfold(before);
                execute();
                simp();
            }
        }
    }

    // Assigning the field drops its old value in place, which the `take`
    // left `None`; the taken box drops at scope end.
    fn put(&mut self, x: u32) {
        owns self.slot;
        consumes before: slot(self.slot);
        produces after: slot(self.slot);
        ensures after.value == Option<u32>::Some(x);
    } by {
        match before.value {
            Option::None => {
                let {} = unfold(before);
                execute();
                let after = fold(slot(self.slot), { value: Option<u32>::Some(x) }, {});
            }
            Option::Some(v) => {
                let {} = unfold(before);
                execute();
                let after = fold(slot(self.slot), { value: Option<u32>::Some(x) }, {});
            }
        }
    }
}
