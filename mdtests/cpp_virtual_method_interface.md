# A call through a C++ virtual method assumes its contract, which each override refines

A virtual method's contract is its interface. A call through it, by a
reference to the base or through `this`, is checked against that contract,
whichever override the object's dynamic type selects. A pure virtual method
has no body, so its contract is declared in an imported `.interface.click`
file. Each override inherits the interface's guarantees and proves them.
`Square::area` inherits the base preconditions and adds a guarantee for its
exact result. `Tile::area` overrides `Square::area` and inherits that exact
result. A `Square` reference converts to the `Shape` base a callee takes.

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
import "interfaces/cpp_virtual_method.interface.click";
verifying "shapes.cpp";
int Shape::twice(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
}
int Square::area(int scale) const {
    ensures result == scale + 1;
}
int Tile::area(int scale) const {
}
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
}
int caller(const Square& square, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures 0 < result;
}
```

```expect
pass
```
