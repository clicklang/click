# A C++ class's const method keeps every field of its object

`Square::area` is `const`, so its contract on `Square`'s memory only
views it: a caller keeps every field across the call, not only the class
block's definitions. After `sq.area(scale)`, the destructor still finds
`log` pointing at `out`, and writes the side back.

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
int caller(int& out, int scale) noexcept {
    Square sq(out, 3);
    return sq.area(scale);
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
