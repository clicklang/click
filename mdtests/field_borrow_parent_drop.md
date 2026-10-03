# Updated fields are observed by the parent cleanup

This isolates the shared memory checker used by Rust field borrows. Updating a guard's
saved field to 42 must be observed by its cleanup through the stored pointer.
This pins the alias/snapshot part of the checker gap; call-havoc cache
invalidation has a separate kernel regression. The ordinary nested Rust Guard
source remains covered by the Rust import integration regression.

```cpp filename=field_drop.cpp function=cleanup profile=scalar_int32
struct Guard {
    int* slot;
    int saved;
    explicit Guard(int& value) noexcept : slot(&value), saved(1) {}
    ~Guard() noexcept { *slot = saved; }
};
int cleanup(int& value) {
    {
        Guard parent(value);
        parent.saved = 42;
    }
    return value;
}
```

```click
verifying "field_drop.cpp";
void Guard_constructor(struct Guard* self, int32* value) {
    owns &self->slot;
    owns self->saved;
    ensures self->slot == value;
    ensures self->saved == 1;
} by { execute(); simp(); }
void Guard_destructor(struct Guard* self) {
    owns &self->slot;
    owns self->saved;
    owns self->slot[0..1];
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures self->slot[0] == old(self->saved);
} by { execute(); simp(); }
int32 cleanup(int32* value) {
    owns value[0..1];
    ensures value[0] == 42;
} by { execute(); simp(); }
```

```expect
pass
```
