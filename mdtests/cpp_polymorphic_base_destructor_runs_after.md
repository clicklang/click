# A C++ polymorphic base's destructor runs after the derived one's body

`Square`'s destructor writes its `side` through the pointer its base holds,
then the base's own destructor runs on the base subobject, as C++ destroys
an object, and writes 9. `Square`'s destructor contract owns the base's
fields as `this->base.log` and ensures what the base destructor ensures, so
the caller knows `out` ends as 9.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
    int* log;
    explicit Shape(int& out) noexcept : log(&out) {}
    virtual ~Shape() noexcept { *log = 9; }
    virtual int area(int scale) const noexcept = 0;
};
struct Square : Shape {
    int side;
    explicit Square(int& out, int s) noexcept : Shape(out), side(s) {}
    ~Square() noexcept override { *log = side; }
    int area(int scale) const noexcept override { return side + scale; }
};
int caller(int& out, int scale) noexcept {
    Square sq(out, 3);
    sq.side = scale;
    return 0;
}
```

```click
verifying "shapes.cpp";
Shape::Shape(int32& out) {
    owns this->log;
    ensures this->log == &out;
} by { execute(); simp(); }
Shape::~Shape() {
    owns this->log;
    owns this->log[0..1];
    ensures this->log == old(this->log);
    ensures this->log[0] == 9;
} by { execute(); simp(); }
Square::Square(int32& out, int32 s) {
    owns this->base.log;
    owns this->side;
    ensures this->base.log == &out;
    ensures this->side == s;
} by { execute(); simp(); }
Square::~Square() {
    owns this->base.log;
    owns this->side;
    owns this->base.log[0..1];
    ensures this->base.log == old(this->base.log);
    ensures this->base.log[0] == 9;
} by { execute(); simp(); }
int caller(int32& out, int scale) {
    owns out;
    ensures result == 0;
    ensures out == 9;
} by { execute(); simp(); }
```

```expect
pass
```
