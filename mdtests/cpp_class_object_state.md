# A C++ class's object state is defined by each class passed as it

A class block declares model functions of a polymorphic class's object,
`class Shape { function size(this) -> int32; }`. Its virtual methods'
contracts, and a function taking `const Shape&`, read `size(this)` or
`size(shape)` as the object's state, which the call keeps. A class passed as
a `Shape` defines the functions on its own memory, `class Square : Shape {
function size(this) -> int32 { this->side } }`: its override is verified on
that memory, inheriting the interface read through the definition, and a
caller passing a `Square` as a `Shape` knows its size is its `side`.
`Shape::twice` reaches `area` through `this`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
    int twice(int scale) const noexcept { return area(scale); }
};
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return side + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.twice(scale);
}
int caller(const Square& square, int scale) noexcept {
    return total(square, scale);
}
```

```click
verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
}
extern int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(this) and size(this) <= 100;
    ensures result == size(this) + scale;
}
int Shape::twice(int scale) const {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(this) and size(this) <= 100;
    ensures result == size(this) + scale;
} by { execute(); simp(); }
class Square : Shape {
    function size(this) -> int32 { this->side }
}
int Square::area(int scale) const {
} by { execute(); simp(); }
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }
int caller(const Square& square, int scale) {
    owns square;
    requires 0 <= scale and scale <= 100;
    requires 0 <= square.side and square.side <= 100;
    ensures result == square.side + scale;
} by { execute(); simp(); }
```

```expect
pass
```
