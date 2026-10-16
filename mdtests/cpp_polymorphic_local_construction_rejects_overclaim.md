# A C++ polymorphic local keeps only what its constructor ensures

The constructor ensures `side == s`, so a caller claiming a different
`side` after `Square sq(3);` is refused.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    explicit Square(int s) noexcept : side(s) {}
    int area(int scale) const noexcept override { return side + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.area(scale);
}
int caller(int scale) noexcept {
    Square sq(3);
    int first = total(sq, scale);
    return sq.side;
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
class Square : Shape {
    function size(this) -> int32 { this->side }
}
Square::Square(int32 s) {
    owns this->side;
    ensures this->side == s;
} by { execute(); simp(); }
int Square::area(int scale) const {
} by { execute(); simp(); }
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }
int caller(int scale) {
    requires 0 <= scale and scale <= 100;
    ensures result == 4;
} by { execute(); simp(); }
```

```expect
fail: `ensures result == 4` failed for `caller.ensures_0`
```
