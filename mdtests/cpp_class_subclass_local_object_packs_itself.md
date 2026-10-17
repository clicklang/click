# A complete object of a class another derives from is packed as its own object

`Square` is a base of `BigSquare`, so a `Square&` holds the `Shape` object
of whichever class it refers to. `caller`'s local `sq` is a complete
`Square`, so the importer places `Square__click_pack_const__Square` where it
is passed as a `const Square&`, making the object from `sq`'s memory with
`Square`'s definitions.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int color;
    explicit Square(int s) noexcept : side(s), color(0) {}
    int area(int scale) const noexcept override { return side + scale; }
};
struct BigSquare : Square {
    int extra;
    int area(int scale) const noexcept override { return side + extra + scale; }
};
int through_square(const Square& square, int scale) noexcept {
    return square.area(scale);
}
int caller(int scale) noexcept {
    Square sq(3);
    return through_square(sq, scale);
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
    owns this->color;
    ensures this->side == s;
    ensures this->color == 0;
} by { execute(); simp(); }
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
int caller(int scale) {
    requires 0 <= scale and scale <= 100;
    ensures result == 3 + scale;
} by { execute(); simp(); }
```

```expect
pass
```
