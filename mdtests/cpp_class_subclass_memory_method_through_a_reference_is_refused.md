# A reference to a class another derives from cannot call its memory methods

`through_square` takes a `const Square&`, which may be a `BigSquare`, so it
holds `Shape`'s object rather than `Square`'s memory. `Square::doubled` is
stated on that memory, so calling it through the reference is refused,
naming what the reference holds.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    int area(int scale) const noexcept override { return side + scale; }
    int doubled() const noexcept { return side + side; }
};
struct BigSquare : Square {
    int extra;
    int area(int scale) const noexcept override { return side + extra + scale; }
};
int through_square(const Square& square, int scale) noexcept {
    int twice = square.doubled();
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
int Square::doubled() const {
    requires 0 <= this->side and this->side <= 100;
    ensures result == this->side + this->side;
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
fail: `through_square` calls `Square::doubled` on `square`, a reference to `Square`, which may be an object of a class deriving from it, such as `BigSquare`
```
