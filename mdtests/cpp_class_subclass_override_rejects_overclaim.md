# A subclass's override that breaks the object class's interface is refused

`BigSquare` redefines `Shape`'s `size` as `side + extra`, so its override of
`area` must return `size + scale` read with that definition. Returning one
more does not keep `Shape`'s interface, which a call through a `Square&`
that reaches the override assumes.

```cpp filename=shapes.cpp function=through_square profile=normal_only
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
    int area(int scale) const noexcept override { return side + extra + scale + 1; }
};
int through_square(const Square& square, int scale) noexcept {
    return square.area(scale);
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
```

```expect
fail: `ensures result == (old((this->base.side + this->extra)) + scale)` failed for `BigSquare::area.interface_ensures_0`
```
