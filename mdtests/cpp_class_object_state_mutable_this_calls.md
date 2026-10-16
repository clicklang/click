# A C++ method calls a mutating virtual method twice through `this`

`Shape::grow_twice` calls `grow` twice through a mutable `this`. The second
call's precondition on `size(this)` holds through the first call's `ensures`,
and `execute()` proves it there; a caller lends a `Square` and reads back the
side the two calls grew.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual void grow(int delta) noexcept = 0;
    void grow_twice(int delta) noexcept { grow(delta); grow(delta); }
};
struct Square : Shape {
    int side;
    void grow(int delta) noexcept override { side = side + delta; }
};
int caller(Square& square, int delta) noexcept {
    square.grow_twice(delta);
    return square.side;
}
```

```click
verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
}
extern void Shape::grow(int delta) {
    requires 0 <= delta and delta <= 100;
    requires 0 <= size(this) and size(this) <= 1000;
    ensures size(this) == old(size(this)) + delta;
}
void Shape::grow_twice(int delta) {
    requires 0 <= delta and delta <= 100;
    requires 0 <= size(this) and size(this) <= 500;
    ensures size(this) == old(size(this)) + delta + delta;
} by { execute(); simp(); }
class Square : Shape {
    function size(this) -> int32 { this->side }
}
void Square::grow(int delta) {
} by { execute(); simp(); }
int caller(Square& square, int delta) {
    owns square;
    requires 0 <= delta and delta <= 100;
    requires 0 <= square.side and square.side <= 500;
    ensures result == old(square.side) + delta + delta;
} by { execute(); simp(); }
```

```expect
pass
```
