# A C++ polymorphic class's empty virtual destructor runs no proof code

`virtual ~Shape() = default;` makes every class derived from `Shape`
destroy through a virtual destructor. One that is defaulted, implicit or
empty, over fields with trivial destruction and a base of the same kind,
only resets the vtable pointer, which the compiler does and no proof reads,
so `Square sq(3);` leaves scope without a destructor contract.

`Square sq(3);` builds a polymorphic `Square` whose base `Shape` has no
fields or constructor. The compiler sets the vtable pointer, which no field
names and no proof reads; the constructor's contract, verified on the
class's own fields, gives the object's state. The caller passes the object
as a `Shape`, and the call keeps its `side`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual ~Shape() = default;
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    explicit Square(int s) noexcept : side(s) {}
    int area(int scale) const noexcept override { return side + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.area(scale);
}
int caller(int scale) noexcept {
    Square sq(3);
    int first = total(sq, scale);
    return sq.side;
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
    ensures this->side == s;
} by { execute(); simp(); }
int Square::area(int scale) const {
} by { execute(); simp(); }
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }
int caller(int scale) {
    requires 0 <= scale and scale <= 100;
    ensures result == 3;
} by { execute(); simp(); }
```

```expect
pass
```
