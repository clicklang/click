verifying "options.rs";

fn option_values::some_if(x: u32, make: bool) -> Option<u32> {
    ensures make implies result == Option<u32>::Some(x);
    ensures make == false implies result == Option<u32>::None;
} by {
    execute();
    simp();
}

fn option_values::or_zero(o: Option<u32>) -> u32 {
    ensures result == (match o { Option::Some(v) => v, Option::None => 0u32 });
} by {
    execute();
    simp();
}

fn option_values::round(x: u32) -> u32 {
    ensures result == x;
} by {
    execute();
    simp();
}

fn option_values::flag(o: Option<bool>) -> bool {
    ensures result == (match o { Option::Some(b) => b, Option::None => false });
} by {
    execute();
    simp();
}

fn option_values::flagged(x: bool) -> bool {
    ensures result == x;
} by {
    execute();
    simp();
}

// Generic functions over `Option<T>` are verified once with `T` abstract.
fn option_values::wrap<T: Copy>(value: T) -> Option<T> {
    ensures result == Option<T>::Some(value);
} by {
    execute();
    simp();
}

fn option_values::unwrap_or<T: Copy>(o: Option<T>, default: T) -> T {
    ensures result == (match o { Option::Some(v) => v, Option::None => default });
} by {
    execute();
    simp();
}

// The calls at `i32` use those contracts at `Option<i32>`.
fn option_values::defaulted(x: i32) -> i32 {
    ensures result == x;
} by {
    execute();
    simp();
}

// `o?` returns `None` on `None` and otherwise reads `Some`'s payload.
fn option_values::plus_one(o: Option<u32>) -> Option<u32> {
    requires match o { Option::Some(v) => v, Option::None => 0u32 } < 4294967295u32;
    ensures result == (match o { Option::Some(v) => Option<u32>::Some(v + 1u32), Option::None => Option<u32>::None });
} by {
    execute();
    simp();
}

fn option_values::same<T: Copy>(o: Option<T>) -> Option<T> {
    ensures result == o;
} by {
    execute();
    simp();
}

fn option_values::kept(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
} by {
    execute();
    simp();
}

fn option_values::passed(o: Option<u32>) -> Option<u32> {
    ensures result == o;
} by {
    execute();
    simp();
}

// A `match` on a call's result splits the option the call returned.
fn option_values::read_passed(o: Option<u32>) -> u32 {
    ensures result == (match o { Option::Some(v) => v, Option::None => 0u32 });
} by {
    execute();
    simp();
}
