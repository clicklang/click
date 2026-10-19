verifying "shapes.rs";

fn grow(s: Shape) -> Shape {
    requires match s { Shape::Circle(r) => r, Shape::Rect(w, h) => 0u32, Shape::Empty => 0u32 } < 4294967295u32;
    ensures result == match s {
        Shape::Circle(r) => Shape::Circle(r + 1u32),
        Shape::Rect(w, h) => Shape::Rect(w, h),
        Shape::Empty => Shape::Empty,
    };
} by { execute(); simp(); }
