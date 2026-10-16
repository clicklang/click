# A C++ polymorphic local runs its own destructor's body

`Square` restores a caller's value when it leaves scope, through a virtual
destructor that overrides `Shape`'s protected defaulted one. A local's
destructor is called directly, so its contract is the class's own; the
base's destruction runs no code a proof sees. Here `out` ends as the side
the caller stored.

```cpp filename=shapes.cpp function=caller profile=normal_only
struct Shape {
protected:
    virtual ~Shape() = default;
public:
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
    sq.side = scale;
    return 0;
}
```

```click
verifying "shapes.cpp";
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
int caller(int32& out, int scale) {
    owns out;
    requires 0 <= scale and scale <= 100;
    ensures result == 0;
    ensures out == scale;
} by { execute(); simp(); }
```

```expect
pass
```
