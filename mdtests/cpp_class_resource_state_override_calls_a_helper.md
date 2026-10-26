# An override holding a class's resource calls a method that states its own

`Boxed` holds its value behind a pointer, in the resource its `class` block
names, `resource state: cell(this->slot);`. Its override `set` holds that
resource beside `*this`, as every override of an object class method does,
and calls `write`, a method of the class that overrides nothing and states
the cell it consumes and produces itself. The override hands `state` to
`write` as its `before` and takes `write`'s `after` back as `state`.

```cpp filename=boxed.cpp function=through profile=normal_only
struct Store {
    virtual void set(int v) noexcept = 0;
};

struct Boxed : Store {
    int* slot;
    void write(int v) noexcept { *slot = v; }
    void set(int v) noexcept override { write(v); }
};

void put(Store& store, int x) noexcept {
    store.set(x);
}

void through(Boxed& boxed, int x) noexcept {
    put(boxed, x);
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
class Boxed : Store {
    resource state: cell(this->slot);
    function held(this) -> int32 { state.value }
}
void Boxed::write(int v) {
    consumes before: cell(this->slot);
    produces after: cell(this->slot);
    ensures after.value == v;
} by {
    unfold(before);
    execute();
    let after = fold(cell(this->slot), { value: v });
}
void Boxed::set(int v) {
} by { execute(); solve(); }
void put(Store& store, int x) {
    ensures held(store) == x;
} by { execute(); solve(); }
void through(Boxed& boxed, int x) {
    owns boxed;
    owns state: cell(boxed.slot);
    ensures state.value == x;
} by { execute(); solve(); }
```

```expect
pass
```
