# A call inside C++ cleanup spells its requirement

A local with a destructor wraps the calls after it in a cleanup edge that
destroys it when a call throws. The call under that wrapper is still the
source call: its precondition is spelled from the callee's written clause, so
the implicit `solve` a bare `step()` runs can prove it, as for a plain call.

```cpp filename=cleanup_requirement.cpp function=caller profile=normal_only
struct Cell { int value; };
struct Guard { int value = 0; ~Guard() noexcept { value = 0; } };
void set(Cell* cell) noexcept { cell->value = 1; }
int caller(Cell* cell) noexcept { Guard guard; set(cell); return 1; }
```

```click
verifying "cleanup_requirement.cpp";
void set(Cell* cell) {
    owns *cell;
    requires cell->value < 10;
    ensures cell->value == 1;
}
Guard::~Guard() { owns *this; }
int32 caller(Cell* cell) {
    owns *cell;
    requires cell->value == 0;
    ensures cell->value == 1;
} by {
    step();
    step();
    step();
    step_until(function.exit);
}
```

```expect
pass
```
