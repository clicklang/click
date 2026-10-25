# A call through a reference to a class another derives from keeps the method's contract

`Tile` derives from `Square` and overrides `area`, so `caller`'s call
through a `const Square&` may run either. Without object state, the
importer's dispatch `Square__click_dispatch__area` has the contract of
`Square::area`, which `Tile::area` refines, so the caller knows the exact
result.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return scale + 1; }
};
struct Tile : Square {
    int area(int scale) const noexcept override { return 1 + scale; }
};
int caller(const Square& square, int scale) noexcept {
    return square.area(scale);
}
```

```click
verifying "shapes.cpp";
extern int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result and result <= 2000;
}
int Square::area(int scale) const {
    ensures to_integer(result) == to_integer(scale + 1);
}
int Tile::area(int scale) const {
}
int caller(const Square& square, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures to_integer(result) == to_integer(scale + 1);
}
```

```expect
pass
```
