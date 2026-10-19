//! A crate enum, constructed, passed, returned and matched.

pub enum Shape {
    Circle(u32),
    Rect { width: u32, height: u32 },
    Empty,
}

pub fn square(side: u32) -> Shape {
    Shape::Rect { width: side, height: side }
}

pub fn perimeter(s: Shape) -> u32 {
    match s {
        Shape::Circle(r) => r * 6,
        Shape::Rect { width, height } => (width + height) * 2,
        Shape::Empty => 0,
    }
}

pub fn grow(s: Shape) -> Shape {
    match s {
        Shape::Circle(r) => Shape::Circle(r + 1),
        other => other,
    }
}

pub fn radius(s: Shape) -> u32 {
    if let Shape::Circle(r) = s { r } else { 0 }
}

pub fn is_empty(s: Shape) -> bool {
    matches!(s, Shape::Empty)
}

pub fn classify(x: u32) -> u32 {
    match x {
        0 => 10,
        1 | 2 => 20,
        _ => 30,
    }
}
