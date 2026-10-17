# A subclass cannot inherit a method whose interface reads a function it redefines

`BigSquare` redefines `tint` as its own `extra`, but inherits
`Square::shade`, whose proof reads `tint` as `color`. A call through `Shape`
on a `BigSquare` would run `Square::shade` and return `color` where the
interface promises `extra`, so the inheritance is refused, naming both
classes: `BigSquare` overrides `shade`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int shade() const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    int shade() const noexcept override { return color; }
};
struct BigSquare : Square {
    int extra;
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
    return second;
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
    function tint(this) -> int32 { this->extra }
}
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
fail: `BigSquare` inherits `Square::shade`, whose interface reads `tint`, which `BigSquare` defines otherwise than `Square`
```
