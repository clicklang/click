# A C++ override cannot refuse a call its virtual method allows

A call through `Shape::area` may pass any `scale` its contract allows and
reach `Square::area`. An override whose `requires` does not follow from the
interface's does not refine it, and is refused naming both.

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
    requires 0 <= scale and scale <= 10;
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
fail: `Square_area` does not refine the virtual method `Shape_area` it overrides
```
