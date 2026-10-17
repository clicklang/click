# A subclass of a defining class redefines the object state and overrides

`BigSquare` derives from `Square`, which defines `Shape`'s `size` as its
`side`. `BigSquare` redefines `size` as `side + extra` and overrides `area`,
which keeps `Shape`'s interface read with that definition. `through_square`
takes a `const Square&`, which may refer to a `BigSquare`: it holds the
`Shape` object, and its call of `area` is checked against `Shape`'s
interface. `caller` passes a `BigSquare`, packed with its own definitions.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    int area(int scale) const noexcept override { return side + scale; }
};
struct BigSquare : Square {
    int extra;
    int area(int scale) const noexcept override { return side + extra + scale; }
};
int through_square(const Square& square, int scale) noexcept {
    return square.area(scale);
}
int caller(BigSquare& big, int scale) noexcept {
    return through_square(big, scale);
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
int Square::area(int scale) const {
} by { execute(); simp(); }
class BigSquare : Square {
    function size(this) -> int32 { this->base.side + this->extra }
}
int BigSquare::area(int scale) const {
} by { execute(); simp(); }
int through_square(const Square& square, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(square) and size(square) <= 100;
    ensures result == size(square) + scale;
} by { execute(); simp(); }
int caller(BigSquare& big, int scale) {
    owns big;
    requires 0 <= scale and scale <= 100;
    requires 0 <= big.base.side + big.extra and big.base.side + big.extra <= 100;
    ensures result == big.base.side + big.extra + scale;
} by { execute(); simp(); }
```

```expect
pass
```
