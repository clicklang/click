# A lent C++ object's memory comes back with its new state

A caller that lends a `Square` as a `Shape&` gets back memory whose
definition is the object's new state, and nothing of the field it lent: it
cannot claim `square.side` kept its value at entry.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual void set(int half) noexcept = 0;
};
struct Square : Shape {
    int side;
    void set(int half) noexcept override { side = half + half; }
};
void reset(Shape& shape, int half) noexcept {
    shape.set(half);
}
int caller(Square& square, int half) noexcept {
    reset(square, half);
    return square.side;
}
```

```click
verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
}
extern void Shape::set(int half) {
    requires 0 <= half and half <= 50;
    ensures size(this) == half + half;
}
class Square : Shape {
    function size(this) -> int32 { this->side }
}
void Square::set(int half) {
} by { execute(); simp(); }
void reset(Shape& shape, int half) {
    requires 0 <= half and half <= 50;
    ensures size(shape) == half + half;
} by { execute(); simp(); }
int caller(Square& square, int half) {
    owns square;
    requires 0 <= half and half <= 50;
    ensures result == old(square.side);
} by { execute(); simp(); }
```

```expect
fail: caller.ensures_0
```
