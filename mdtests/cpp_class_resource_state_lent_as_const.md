# A class holding its state in a resource is lent as a `const` reference

`Boxed` keeps its value behind a pointer, in the resource its `class` block
names, `resource state: cell(this->slot);`. Passing a `const Boxed&` as a
`const Store&` lends the object's memory to a resource the `const` pack
produces, and the pack consumes `state` into the object, so nothing can
change the cell while `read` holds the object. The `const` unpack gives
`state` back at the pointer it had at entry, `cell(old(object->slot))`: the
caller's view of `slot` is the lent resource's, which the unpack consumes, so
that read is made with the authority the caller held at entry. `peek` knows
the cell holds what `read` returned, and that it is unchanged.

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
    execute();
    let state = fold(cell(this->slot), { value: old(state.value) });
}
int read(const Store& store) {
    ensures result == held(store);
} by { execute(); simp(); }
int peek(const Boxed& boxed) {
    owns boxed;
    owns state: cell(boxed.slot);
    ensures result == state.value;
    ensures state.value == old(state.value);
} by { execute(); simp(); }
```

```expect
pass
```
