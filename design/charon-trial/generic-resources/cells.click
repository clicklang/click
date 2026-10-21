verifying "cells.rs";

resource cell<T: Copy>(c: *mut generic_resources::Cell<T>) {
    field value: T;
    owns c.value;
    fact c.value == value;
}

fn generic_resources::write<T: Copy>(cell: &mut generic_resources::Cell<T>, value: T) {
    consumes before: cell<T>(cell);
    produces after: cell<T>(cell);
    ensures after.value == value;
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell<T>(cell), { value: value }, {});
}

fn generic_resources::read<T: Copy>(cell: &generic_resources::Cell<T>) -> T {
    consumes before: cell<T>(cell);
    produces after: cell<T>(cell);
    ensures after.value == old(before.value);
    ensures result == old(before.value);
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell<T>(cell), { value: old(before.value) }, {});
}

fn generic_resources::set_and_get(cell: &mut generic_resources::Cell<u32>, x: u32) -> u32 {
    consumes before: cell<u32>(cell);
    produces after: cell<u32>(cell);
    ensures result == x;
    ensures after.value == x;
} by {
    execute();
    simp();
}
