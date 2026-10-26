verifying "options.rs";

fn option_values::some_if(x: u32, make: bool) -> Option<u32> {
    ensures make implies result == Option<u32>::Some(x);
    ensures make == false implies result == Option<u32>::None;
}

fn option_values::or_zero(o: Option<u32>) -> u32 {
    ensures result == (match o { Option::Some(v) => v, Option::None => 0u32 });
}

fn option_values::round(x: u32) -> u32 {
    ensures result == x;
}

fn option_values::flag(o: Option<bool>) -> bool {
    ensures result == (match o { Option::Some(b) => b, Option::None => false });
}

fn option_values::flagged(x: bool) -> bool {
    ensures result == x;
}

// Generic functions over `Option<T>` are verified once with `T` abstract.
fn option_values::wrap<T: Copy>(value: T) -> Option<T> {
    ensures result == Option<T>::Some(value);
}

fn option_values::unwrap_or<T: Copy>(o: Option<T>, default: T) -> T {
    ensures result == (match o { Option::Some(v) => v, Option::None => default });
}

// The calls at `i32` use those contracts at `Option<i32>`.
fn option_values::defaulted(x: i32) -> i32 {
    ensures result == x;
}

// `o?` returns `None` on `None` and otherwise reads `Some`'s payload.
fn option_values::plus_one(o: Option<u32>) -> Option<u32> {
    requires match o { Option::Some(v) => v, Option::None => 0u32 } < 4294967295u32;
    ensures result == (match o { Option::Some(v) => Option<u32>::Some(v + 1u32), Option::None => Option<u32>::None });
}

fn option_values::same<T: Copy>(o: Option<T>) -> Option<T> {
    ensures result == o;
}

fn option_values::kept(x: u32) -> Option<u32> {
    ensures result == Option<u32>::Some(x);
}

fn option_values::passed(o: Option<u32>) -> Option<u32> {
    ensures result == o;
}

// A `match` on a call's result splits the option the call returned.
fn option_values::read_passed(o: Option<u32>) -> u32 {
    ensures result == (match o { Option::Some(v) => v, Option::None => 0u32 });
}

// Two `?`s: each `None` returns `None` through the same tail.
fn option_values::sum(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    requires match a { Option::Some(v) => v, Option::None => 0u32 } < 2147483648u32;
    requires match b { Option::Some(v) => v, Option::None => 0u32 } < 2147483648u32;
    ensures result == (match a {
        Option::Some(x) => (match b { Option::Some(y) => Option<u32>::Some(x + y), Option::None => Option<u32>::None }),
        Option::None => Option<u32>::None,
    });
} by {
    match a {
        Option::Some(p) => {
            match b {
                Option::Some(q) => { step_until(function.exit); solve(); },
                Option::None => { step_until(function.exit); solve(); },
            }
        },
        Option::None => { step_until(function.exit); solve(); },
    }
}
