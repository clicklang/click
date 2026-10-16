# A C++ class's object state through a mutable receiver and reference

A non-`const` virtual method of a class whose object carries state, and a
`Shape&` parameter, may change the state: their `ensures` read `size(this)`
as the new state and `old(size(this))` as the state at entry. An override
is verified on its class's memory against the interface read through its
definition, and a caller that lends a `Square` as a `Shape&` gets back
memory whose definition is the object's new state.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual void set(int half) noexcept = 0;
    virtual void grow(int delta) noexcept = 0;
};
struct Square : Shape {
    int side;
    void set(int half) noexcept override { side = half + half; }
    void grow(int delta) noexcept override { side = side + delta; }
};
void bump(Shape& shape, int delta) noexcept {
    shape.grow(delta);
}
void reset(Shape& shape, int half) noexcept {
    shape.set(half);
}
int caller(Square& square, int delta, int half) noexcept {
    bump(square, delta);
    reset(square, half);
    return square.side;
}
```

```click
verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
}
extern void Shape::set(int half) {
    requires 0 <= half and half <= 50;
    ensures size(this) == half + half;
}
extern void Shape::grow(int delta) {
    requires 0 <= delta and delta <= 100;
    requires 0 <= size(this) and size(this) <= 1000;
    ensures size(this) == old(size(this)) + delta;
}
class Square : Shape {
    function size(this) -> int32 { this->side }
}
void Square::set(int half) {
} by { execute(); simp(); }
void Square::grow(int delta) {
} by { execute(); simp(); }
void bump(Shape& shape, int delta) {
    requires 0 <= delta and delta <= 100;
    requires 0 <= size(shape) and size(shape) <= 1000;
    ensures size(shape) - delta == old(size(shape));
} by { execute(); simp(); }
void reset(Shape& shape, int half) {
    requires 0 <= half and half <= 50;
    ensures size(shape) == half + half;
} by { execute(); simp(); }
int caller(Square& square, int delta, int half) {
    owns square;
    requires 0 <= delta and delta <= 100;
    requires 0 <= half and half <= 50;
    requires 0 <= square.side and square.side <= 1000;
    ensures result == half + half;
} by { execute(); simp(); }
```

```expect
pass
```
