verifying "shapes.rs";

// `Shape` is the `spec enum` the import declares from the Rust enum. A struct
// variant's fields are positional, in declaration order.

fn square(side: u32) -> Shape {
    ensures result == Shape::Rect(side, side);
}

// The omitted proof's implicit tail splits the Rust `match` with a proof
// `match` on `s`. Each arm learns what the requirements say about its fields.
fn perimeter(s: Shape) -> u32 {
    requires match s { Shape::Circle(r) => r, Shape::Rect(w, h) => w, Shape::Empty => 0u32 } <= 1000u32;
    requires match s { Shape::Circle(r) => r, Shape::Rect(w, h) => h, Shape::Empty => 0u32 } <= 1000u32;
    // The perimeter is the `u32` value the Rust arms compute.
    let perimeter: u32 = match s {
        Shape::Circle(r) => r * 6u32,
        Shape::Rect(w, h) => (w + h) * 2u32,
        Shape::Empty => 0u32,
    };
    ensures result == perimeter;
}

fn grow(s: Shape) -> Shape {
    requires match s { Shape::Circle(r) => r, Shape::Rect(w, h) => 0u32, Shape::Empty => 0u32 } < 4294967295u32;
    ensures result == match s {
        Shape::Circle(r) => Shape::Circle(r + 1u32),
        Shape::Rect(w, h) => Shape::Rect(w, h),
        Shape::Empty => Shape::Empty,
    };
}

// The split the implicit tail makes, written out.
fn radius(s: Shape) -> u32 {
    ensures result == match s { Shape::Circle(r) => r, Shape::Rect(w, h) => 0u32, Shape::Empty => 0u32 };
} by {
    match s {
        Shape::Circle(r) => { step_until(function.exit); solve(); },
        Shape::Rect(w, h) => { step_until(function.exit); solve(); },
        Shape::Empty => { step_until(function.exit); solve(); },
    }
}

fn is_empty(s: Shape) -> bool {
    ensures result == (s == Shape::Empty);
}

fn classify(x: u32) -> u32 {
    ensures x == 0u32 implies result == 10u32;
    ensures (x == 1u32 or x == 2u32) implies result == 20u32;
    ensures x > 2u32 implies result == 30u32;
}

// A `bool` field is stored as a `bool`, as an assignment stores one.
fn light(on: bool) -> Light {
    ensures on implies result == Light::On(true);
    ensures on == false implies result == Light::Off;
}
