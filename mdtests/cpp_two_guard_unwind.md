# C++ two-guard cleanup on a caught cross-call exception

Probe for the control-flow demo: two `Restore` guards over two distinct
cells, constructed inside a `try`, then a helper call that either returns
normally or throws `int`. Both guards must be destroyed in reverse
construction order before the caller observes the cells, on the normal path
and before the handler observes them on the exceptional path. The guard shape
is copied unchanged from `cpp_one_guard_unwind.md` so that guard count is the
only new variable; only the second guard and the separation between the two
cells are new.

```cpp filename=guarded2.cpp function=guarded2 profile=scalar_int32
struct Restore {
    int* pointer;
    int saved;

    explicit Restore(int* slot) noexcept : pointer(slot), saved(*slot) {
        *pointer = 9;
    }

    ~Restore() noexcept { *pointer = saved; }
};

int helper(bool should_throw) {
    if (should_throw) { throw 7; }
    return 5;
}

int guarded2(int& first_cell, int& second_cell, bool should_throw) {
    try {
        Restore first(&first_cell);
        Restore second(&second_cell);
        helper(should_throw);
    } catch (int caught) {
        return first_cell;
    }
    return first_cell;
}
```

```click
verifying "guarded2.cpp";

void Restore_constructor(struct Restore* this, int32* slot) {
    owns this->pointer;
    owns this->saved;
    owns slot[0..1];
    ensures this->pointer == slot;
    ensures this->saved == old(slot[0]);
    ensures slot[0] == 9;
    ensures separate(memory(*this), memory(this->pointer[0..1]));
} by {
    execute();
    simp();
}

void Restore_destructor(struct Restore* this) {
    requires separate(memory(*this), memory(this->pointer[0..1]));
    owns this->pointer;
    owns this->saved;
    owns this->pointer[0..1];
    ensures this->pointer == old(this->pointer);
    ensures this->saved == old(this->saved);
    ensures this->pointer[0] == old(this->saved);
} by {
    execute();
    simp();
}

int32 helper(bool should_throw) throws int32 {
    ensures result == 5;
    exceptional ensures exception == 7;
}

int32 guarded2(int32& first_cell, int32& second_cell, bool should_throw) {
    owns first_cell;
    owns second_cell;
    requires separate(memory(first_cell), memory(second_cell));
    ensures result == old(first_cell);
    ensures first_cell == old(first_cell);
    ensures second_cell == old(second_cell);
} by {
    step();
    step();
    step();
    step();
    outcomes {
        returned => {
            step();
            step();
            have second_cell == old(second_cell) by { simp(); }
            execute();
            simp();
        }
        threw => {
            step();
            step();
            have second_cell == old(second_cell) by { simp(); }
            execute();
            simp();
        }
    }
}
```

```expect
pass
```
