# A C++ class may hold its object's state in a resource beside its memory

`Boxed` keeps its value behind a pointer, in memory its fields do not
cover. Its `class` block names the resource holding that memory, `resource
state: cell(this->slot);`, and defines `held` from its field, `state.value`.
Each override of a `Store` method holds the resource beside `*this`, so its
proof unfolds and folds it as it writes or reads the cell. Where a `Boxed&`
becomes a `Store&`, the pack consumes the resource with the memory and the
unpack gives it back holding the object's new state, so `through` knows the
cell holds `x`.

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
pass
```
