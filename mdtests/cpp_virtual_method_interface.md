# A call through a C++ virtual method assumes its contract, which each override refines

A virtual method's contract is its interface. A call through it, by a
reference to the base or through `this`, is checked against that contract,
whichever override the object's dynamic type selects. A pure virtual method
has no body, so its contract is written `extern`. Each override inherits the
interface's guarantees, which its own proof establishes, and its `requires`
must follow from the interface's: `Square::area` states nothing and inherits
both, and `Tile::area` overrides `Square::area`, so it inherits that
override's exact result. A `Square` reference converts to the `Shape` base a
callee takes.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
    int twice(int scale) const noexcept { return area(scale) + area(scale); }
};
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return scale + 1; }
};
struct Tile : Square {
    int area(int scale) const noexcept override { return 1 + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.twice(scale);
}
int caller(const Square& square, int scale) noexcept {
    return total(square, scale);
}
```

```click
verifying "shapes.cpp";
extern int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result and result <= 2000;
}
int Shape::twice(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
} by { execute(); simp(); }
int Square::area(int scale) const {
    ensures result == scale + 1;
} by { execute(); simp(); }
int Tile::area(int scale) const {
} by { execute(); simp(); }
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
} by { execute(); simp(); }
int caller(const Square& square, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
} by { execute(); simp(); }
```

```expect
pass
```
