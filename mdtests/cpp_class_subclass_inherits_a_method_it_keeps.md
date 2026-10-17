# A subclass inherits a defining class's method whose interface it reads alike

`BigSquare` redefines `Shape`'s `size` but inherits `tint` and
`Square::shade`, whose interface reads only `tint`. On a `BigSquare`, a
call through `Shape` or `Square` that reaches `Square::shade` runs it on
the `Square` part, where `tint` is the same `color` its proof reads, so the
inheritance is accepted without verifying `Square::shade` again. `caller`
lends a `BigSquare` through both references. `BigSquare::brighter` calls
`Square`'s own `hue` through `this`, which runs on `Square`'s part as
memory, unpacked.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int shade() const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    int shade() const noexcept override { return color; }
    int hue() const noexcept { return color; }
};
struct BigSquare : Square {
    int extra;
    int brighter() const noexcept { return hue(); }
};
int through_shape(const Shape& shape) noexcept {
    return shape.shade();
}
int through_square(const Square& square) noexcept {
    return square.shade();
}
int caller(BigSquare& big) noexcept {
    int first = through_shape(big);
    int second = through_square(big);
    return big.brighter();
}
```

```click
verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
    function tint(this) -> int32;
}
extern int Shape::shade() const {
    ensures result == tint(this);
}
class Square : Shape {
    function size(this) -> int32 { this->side }
    function tint(this) -> int32 { this->color }
}
int Square::shade() const {
} by { execute(); simp(); }
class BigSquare : Square {
    function size(this) -> int32 { this->base.side + this->extra }
}
int Square::hue() const {
    ensures result == this->color;
} by { execute(); simp(); }
int BigSquare::brighter() const {
    ensures result == this->base.color;
} by { execute(); simp(); }
int through_shape(const Shape& shape) {
    ensures result == tint(shape);
} by { execute(); simp(); }
int through_square(const Square& square) {
    ensures result == tint(square);
} by { execute(); simp(); }
int caller(BigSquare& big) {
    owns big;
    ensures result == big.base.color;
} by { execute(); simp(); }
```

```expect
pass
```
