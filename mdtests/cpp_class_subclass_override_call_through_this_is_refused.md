# A method of a class another derives from cannot dispatch through `this`

`Square::twice` is stated on `Square`'s memory, but `this` may be a
`BigSquare`, whose `area` override needs `Shape`'s object. The call is
refused before verification, naming what each side holds; a qualified call,
`this->Square::area(scale)`, would run `Square::area` itself.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    int area(int scale) const noexcept override { return side + scale; }
    int twice(int scale) const noexcept { return area(scale); }
};
struct BigSquare : Square {
    int extra;
    int area(int scale) const noexcept override { return side + extra + scale; }
};
int through_square(const Square& square, int scale) noexcept {
    return square.twice(scale);
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
int Square::twice(int scale) const {
    requires 0 <= scale and scale <= 100;
    requires 0 <= this->side and this->side <= 100;
    ensures result == this->side + scale;
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
fail: `Square::twice` calls `Square::area` through `this`, which may be an object of a class deriving from its class, such as `BigSquare`
```
