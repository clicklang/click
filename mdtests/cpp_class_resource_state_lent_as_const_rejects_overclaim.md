# A `const` reference keeps a class's resource-held state

Lending a `const Boxed&` as a `const Store&` returns `state` holding the value
it had: the object a `const` reference holds keeps its fields, and the
`const` unpack equates the returned cell with them. `peek` claiming the cell
grew is refused.

```cpp filename=boxed.cpp function=peek profile=normal_only
struct Store {
    virtual int get() const noexcept = 0;
};

struct Boxed : Store {
    int* slot;
    int get() const noexcept override { return *slot; }
};

int read(const Store& store) noexcept {
    int got = store.get();
    return got;
}

int peek(const Boxed& boxed) noexcept {
    int got = read(boxed);
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
extern int Store::get() const {
    ensures result == held(this);
}
class Boxed : Store {
    resource state: cell(this->slot);
    function held(this) -> int32 { state.value }
}
int Boxed::get() const {
} by {
    unfold(state);
    step_until(function.exit);
    let state = fold(cell(this->slot), { value: old(state.value) });
}
int read(const Store& store) {
    ensures result == held(store);
}
int peek(const Boxed& boxed) {
    owns boxed;
    owns state: cell(boxed.slot);
    ensures result == state.value;
    ensures state.value == old(state.value) + 1;
}
```

```expect
fail: failed for `peek.ensures_1`
```
