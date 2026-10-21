verifying "boxed.rs";

fn boxed::boxed(x: u32) -> u32 {
    requires x < 100;
    ensures result == x + 1;
} by { execute(); simp(); }

// A box moves out of `make` and into `read` with its allocation and cell:
// `read` frees them when its box is dropped, and `through` holds them only
// between the two calls.
fn boxed::make(x: u32) -> Box<boxed::Cell> {
    produces allocation(result, sizeof(boxed::Cell));
    produces *result;
    ensures aligned(result, 4);
    ensures result.value == x;
} by { execute(); simp(); }

fn boxed::read(b: Box<boxed::Cell>) -> u32 {
    consumes allocation(b, sizeof(boxed::Cell));
    consumes *b;
    ensures result == old(b.value);
} by { execute(); simp(); }

fn boxed::through(x: u32) -> u32 {
    ensures result == x;
} by { execute(); simp(); }

// A `Some` box owns its cell, holding `Some` of its value; `None` is null.
resource cell_box(p: *mut boxed::Cell) {
    field value: Option<u32>;
    match value {
        Option::None => { fact p == 0; },
        Option::Some(v) => {
            owns allocation(p, sizeof(boxed::Cell));
            owns *p;
            fact p != 0;
            fact aligned(p, 4);
            fact p.value == v;
        },
    }
}

fn boxed::maybe(x: u32, make: bool) -> Option<Box<boxed::Cell>> {
    produces cell: cell_box(result);
    ensures make implies cell.value == Option<u32>::Some(x);
    ensures make == false implies cell.value == Option<u32>::None;
} by {
    cases {
        make => {
            execute();
            let cell = fold(cell_box(result), { value: Option<u32>::Some(x) });
            simp();
        }
        not make => {
            execute();
            let cell = fold(cell_box(result), { value: Option<u32>::None });
            simp();
        }
    }
}

fn boxed::value_or(o: Option<Box<boxed::Cell>>, d: u32) -> u32 {
    consumes cell: cell_box(o);
    ensures result == (match old(cell.value) { Option::Some(v) => v, Option::None => d });
} by {
    match cell.value {
        Option::Some(v) => { unfold(cell); execute(); simp(); },
        Option::None => { unfold(cell); execute(); simp(); },
    }
}

fn boxed::maybe_through(x: u32, make: bool) -> u32 {
    ensures make implies result == x;
    ensures make == false implies result == 0;
} by {
    cases {
        make => { execute(); simp(); }
        not make => { execute(); simp(); }
    }
}
