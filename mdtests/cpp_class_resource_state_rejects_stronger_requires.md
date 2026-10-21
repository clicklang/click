# An override holding its state in a resource still refines the interface

`Boxed::set` requires the cell to hold `0`, which `Store::set`'s interface
does not: read through `Boxed`'s definition, `held(this)` is the held
resource's `state.value`, and the stronger `requires` is refused as no
refinement.

```cpp filename=boxed.cpp function=store;through profile=normal_only
struct Store {
    virtual void set(int v) noexcept = 0;
    virtual int get() const noexcept = 0;
};

struct Boxed : Store {
    int* slot;
    void set(int v) noexcept override { *slot = v; }
    int get() const noexcept override { return *slot; }
};

int store(Store& store, int x) noexcept {
    store.set(x);
    int got = store.get();
    return got;
}

int through(Boxed& boxed, int x) noexcept {
    int got = store(boxed, x);
    return got;
}
```

```click
verifying "boxed.cpp";

resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

class Store {
    function held(this) -> int32;
}
extern void Store::set(int v) {
    ensures held(this) == v;
}
extern int Store::get() const {
    ensures result == held(this);
}
class Boxed : Store {
    resource state: cell(this->slot);
    function held(this) -> int32 { state.value }
}
void Boxed::set(int v) {
    requires held(this) == 0;
} by {
    unfold(state);
    execute();
    let state = fold(cell(this->slot), { value: v });
}
int Boxed::get() const {
} by {
    unfold(state);
    execute();
    let state = fold(cell(this->slot), { value: old(state.value) });
}

int store(Store& store, int x) {
    ensures result == x;
    ensures held(store) == x;
} by { execute(); simp(); }

int through(Boxed& boxed, int x) {
    owns boxed;
    owns state: cell(boxed.slot);
    ensures result == x;
    ensures state.value == x;
} by { execute(); simp(); }
```

```expect
fail: `Boxed::set` does not refine the virtual method `Store::set` it overrides
```
