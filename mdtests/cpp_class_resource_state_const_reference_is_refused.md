# A class holding its state in a resource is not lent as a `const` reference

A `const Store&` keeps the object it refers to, and a `const` reference to
a class whose state is in its fields lends the memory for the call, which
nothing can change meanwhile. A resource cannot be lent so: it would have to
stay with the object, out of the caller's hands, for the call. `Boxed`'s
`const` pack therefore admits no call, and passing a `const Boxed&` as a
`const Store&` is refused at it.

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
} by { execute(); simp(); }
```

```expect
fail: precondition clause 1 of `Boxed__click_pack_const__Store`
```
