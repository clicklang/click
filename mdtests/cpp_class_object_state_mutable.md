# A C++ class's object state through a mutable receiver and reference

A non-`const` virtual method of a class whose object carries state, and a
`Shape&` parameter, may change the state: their `ensures` read `size(this)`
as the new state and `old(size(this))` as the state at entry. An override
is verified on its class's memory against the interface read through its
definition, and a caller that lends a `Square` as a `Shape&` gets back
memory whose definition is the object's new state. `Shape::grow_twice`
reaches `grow` through a mutable `this`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual void set(int half) noexcept = 0;
    virtual void grow(int delta) noexcept = 0;
    void grow_twice(int delta) noexcept { grow(delta); grow(delta); }
};
struct Square : Shape {
    int side;
    void set(int half) noexcept override { side = half + half; }
    void grow(int delta) noexcept override { side = side + delta; }
};
void reset(Shape& shape, int half) noexcept {
    shape.set(half);
}
int caller(Square& square, int half) noexcept {
    reset(square, half);
    square.grow_twice(1);
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
void Shape::grow_twice(int delta) {
    requires 0 <= delta and delta <= 100;
    requires 0 <= size(this) and size(this) <= 500;
    ensures size(this) == old(size(this)) + delta + delta;
} by { execute(); simp(); }
class Square : Shape {
    function size(this) -> int32 { this->side }
}
void Square::set(int half) {
} by { execute(); simp(); }
void Square::grow(int delta) {
} by { execute(); simp(); }
void reset(Shape& shape, int half) {
    requires 0 <= half and half <= 50;
    ensures size(shape) == half + half;
} by { execute(); simp(); }
int caller(Square& square, int half) {
    owns square;
    requires 0 <= half and half <= 50;
    ensures result == half + half + 2;
} by { execute(); simp(); }
```

```expect
pass
```
