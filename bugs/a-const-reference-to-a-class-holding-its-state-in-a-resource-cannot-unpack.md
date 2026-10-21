# A `const` reference to a class holding its state in a resource cannot unpack

Soundness: incomplete. The failure refuses a valid program; nothing false
verifies. The `const` pack consumes the class's held resource with the
object, so the callee cannot reach the memory it covers, and the `const`
unpack that should return it is never applied.

`docs/reference/cli/import.md` says a defining class that names the resource
holding its state, `resource state: cell(this->slot);`, has a `const` pack
that consumes the resource and a `const` unpack that returns it with the
definitions equal to the object's kept fields. Passing such a class as a
`const` base reference does not verify: the `const` unpack's produced
resource reads `object->slot` for its argument, and at the unpack the
caller's view of the object's memory is held by the lent resource the unpack
consumes, so the argument cannot be evaluated.

## Reproduction

`boxed.cpp`, a C++ unit with `"functions": ["peek"]`:

```cpp
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

`peek` fails at `Boxed__click_unpack_const__Store(((int32*)&boxed))`:

```text
resource `cell` argument 1 could not be evaluated
required access authority is unavailable
required
views memory(value#1[Int32:0..1], stride=4)
  value#1 = &boxed + 8 bytes
```

Giving the `const` unpack its own `views *object;` instead is refused as
`stable-view this resource shape is outside stable-view support`. Returning
the resource to the caller before the call, so the pack only borrows it, is
unsound: another argument of the same call could consume it and change the
memory while the callee holds an object whose state is fixed.

## Acceptance criteria

- The reproduction verifies as written, with `peek` knowing `result ==
  state.value` and that `state.value` is unchanged.
- A caller claiming `state.value` changed across the call is refused.
- The regression is an mdtest beside
  `mdtests/cpp_generic_class_state_in_a_resource.md`.
