# A C++ polymorphic object's base is built by the base's own constructor

`Square(int s) : Shape(7), side(s)` names its base's constructor first, as
C++ runs it: the importer calls `Shape::Shape` on the base subobject, then
initializes `Square`'s own members. `Square`'s constructor owns the base's
field as `this->base.tag`, lends it to `Shape::Shape`, and ensures what that
constructor ensures.

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
    ensures this->base.tag == 7;
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
pass
```
