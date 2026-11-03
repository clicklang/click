# A call inside C++ cleanup can name its produced resource

The cleanup wrapper must preserve the same resource-binding operation as a
plain call. The named output is used immediately, before the guard is destroyed.

```cpp filename=cleanup.cpp function=caller profile=normal_only
struct Cell { int value; };
struct Guard { int value = 0; ~Guard() noexcept { value = 0; } };
void set(Cell* cell) noexcept { cell->value = 1; }
int caller(Cell* cell) noexcept { Guard guard; set(cell); return 1; }
```

```click
verifying "cleanup.cpp";
resource cell_value(p: Cell*) {
    field value: int32;
    owns *p;
    fact p->value == value;
}
void set(Cell* cell) {
    consumes before: cell_value(cell);
    produces after: cell_value(cell);
    ensures after.value == 1;
} by {
    unfold(before);
    step_until(function.exit);
    let after = fold(cell_value(cell), { value: 1 });
}
Guard::~Guard() { owns *this; }
int32 caller(Cell* cell) {
    consumes before: cell_value(cell);
    produces after: cell_value(cell);
    ensures after.value == 1;
} by {
    step();
    step();
    let { after: after } = step(set, { before: before });
    have after.value == 1 by { assumption(); }
    step_until(function.exit);
}
```

```expect
pass
```
