verifying "refs.rs";

// A reference to an `Option` refers to one `Option` value: `*o` reads,
// writes and matches it.
fn option_refs::take_it(o: &mut Option<u32>) -> Option<u32> {
    owns *o;
    ensures result == old(*o);
    ensures *o == Option<u32>::None;
}

fn option_refs::fill(o: &mut Option<u32>, x: u32) {
    owns *o;
    ensures *o == Option<u32>::Some(x);
}

fn option_refs::peek(o: &Option<u32>) -> u32 {
    views *o;
    ensures result == (match *o { Option::Some(v) => v, Option::None => 0u32 });
}

// A borrowed local keeps its value in memory, where the callees' writes
// through `&mut o` land.
fn option_refs::round(x: u32) -> u32 {
    ensures result == x;
}

fn option_refs::clear(o: &mut Option<u32>) {
    owns *o;
    ensures *o == Option<u32>::None;
}

fn option_refs::cleared(x: u32) -> u32 {
    ensures result == 0u32;
}

// So does a borrowed local of a type parameter, and of an integer.
fn option_refs::put<T: Copy>(slot: &mut T, value: T) {
    owns *slot;
    ensures *slot == value;
}

fn option_refs::replaced<T: Copy>(a: T, b: T) -> T {
    ensures result == b;
}

fn option_refs::replaced_u32(a: u32, b: u32) -> u32 {
    ensures result == b;
}

fn option_refs::bump(x: &mut u32) {
    owns *x;
    ensures *x == 7u32;
}

fn option_refs::bumped() -> u32 {
    ensures result == 7u32;
}
