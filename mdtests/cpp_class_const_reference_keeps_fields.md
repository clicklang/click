# A C++ class passed as a const base reference keeps every field

`total` takes `const Shape&`, so the importer's `const` pack lends `sq`'s
memory, joined from its vtable-pointer bytes and fields, to a resource it
produces beside the `Shape` object, and the `const` unpack releases it.
Nothing can change the memory meanwhile, so the caller keeps every field:
the destructor still finds `log` pointing at `out`.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    virtual ~Shape() = default;
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int* log;
    int side;
    explicit Square(int& out, int s) noexcept : log(&out), side(s) {}
    ~Square() noexcept override { *log = side; }
    int area(int scale) const noexcept override { return side + scale; }
};
int total(const Shape& shape, int scale) noexcept {
    return shape.area(scale);
}
int caller(int& out, int scale) noexcept {
    Square sq(out, 3);
    return total(sq, scale);
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
Square::Square(int32& out, int32 s) {
    owns this->log;
    owns this->side;
    ensures this->log == &out;
    ensures this->side == s;
} by { execute(); simp(); }
Square::~Square() {
    owns this->log;
    owns this->side;
    owns this->log[0..1];
    ensures this->log == old(this->log);
    ensures this->side == old(this->side);
    ensures this->log[0] == old(this->side);
} by { execute(); simp(); }
int Square::area(int scale) const {
} by { execute(); simp(); }
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
} by { execute(); simp(); }
int caller(int32& out, int scale) {
    owns out;
    requires 0 <= scale and scale <= 100;
    ensures result == 3 + scale;
    ensures out == 3;
} by { execute(); simp(); }
```

```expect
pass
```
