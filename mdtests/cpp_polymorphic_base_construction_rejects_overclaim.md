# A C++ derived constructor keeps only what its base's constructor ensures

`Shape(7)` ensures `tag == 7`, so `Square`'s constructor claiming 8 is
refused.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    long long tag;
    explicit Shape(long long t) noexcept : tag(t) {}
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    explicit Square(int s) noexcept : Shape(7), side(s) {}
    int area(int scale) const noexcept override { return side + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.area(scale);
}
int caller(int scale) noexcept {
    Square sq(3);
    return total(sq, scale);
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
Shape::Shape(int64 t) {
    owns this->tag;
    ensures this->tag == t;
} by { execute(); simp(); }
Square::Square(int32 s) {
    owns this->base.tag;
    owns this->side;
    ensures this->base.tag == 8;
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
    ensures result == 3 + scale;
} by { execute(); simp(); }
```

```expect
fail: `ensures this->base.tag == 8` failed for `Square::Square.ensures_0`
```
