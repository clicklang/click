# An override with a mutable receiver establishes its interface's new state

`Square::set` is verified on its class's memory against `Shape::set`'s
interface read through `size(this)`'s definition, `this->side`: an override
storing `half` does not establish `size(this) == half + half`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual void set(int half) noexcept = 0;
};
struct Square : Shape {
    int side;
    void set(int half) noexcept override { side = half; }
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
    ensures result == half + half;
} by { execute(); simp(); }
```

```expect
fail: Square::set.interface_ensures_0
```
