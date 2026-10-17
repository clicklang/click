# A C++ class lent as a const base reference cannot also be handed over

`peek_then_poke(sq, sq)` passes one object as `const Shape& a` and
`Square& s`. The `const` pack keeps `sq` lent while the callee holds `a`,
so the call cannot also take `owns s`: otherwise the callee could change
`side` while `a` claims its size unchanged.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return side + scale; }
};
int peek_then_poke(const Shape& a, Square& s) noexcept {
    s.side = 50;
    return a.area(0);
}
int caller(Square& sq) noexcept {
    return peek_then_poke(sq, sq);
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
int peek_then_poke(const Shape& a, Square& s) {
    owns s;
    requires 0 <= size(a) and size(a) <= 100;
    ensures result == size(a);
} by { execute(); simp(); }
int caller(Square& sq) {
    owns sq;
    requires 0 <= sq.side and sq.side <= 100;
    ensures result == sq.side;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `owns sq`
```
