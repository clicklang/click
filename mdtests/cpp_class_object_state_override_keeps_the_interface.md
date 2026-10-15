# A C++ override meets its interface read through its class's definitions

`Square::area` inherits `Shape::area`'s guarantee with `size(this)` read as
`Square`'s definition, `this->side`: its result must be `side + scale`. Its
body ignores `side`, and its proof fails on the inherited guarantee.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
    int twice(int scale) const noexcept { return area(scale); }
};
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return scale + 1; }
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
fail: Square_area.interface_ensures_0
```
