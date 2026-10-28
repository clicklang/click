# Nested field aliases retain their scalar reads after a call

The postcondition reads through a stored pointer while the next call reads the
field directly. Their distinct canonical projections must meet in the shared
equality graph after the address equality is established.

```c filename=guard.c
struct guard { int32* slot; int32 saved; };
void drop(struct guard* self) { *self->slot = self->saved; }
void cleanup(int32* value) {
    struct guard first;
    first.slot = value;
    first.saved = 1;
    struct guard second;
    second.slot = &first.saved;
    second.saved = 42;
    drop(&second);
    drop(&first);
}
```

```click
verifying "guard.c";
void drop(struct guard* self) {
    requires separate(memory(*self), memory(self->slot[0..1]));
    owns self->slot;
    owns self->saved;
    owns *self->slot;
    ensures self->slot == old(self->slot);
    ensures self->saved == old(self->saved);
    ensures *self->slot == old(self->saved);
}
void cleanup(int32* value) {
    owns *value;
    ensures *value == 42;
} by {
    step_until(statement(7));
    have *second.slot == at(statement(6).entry, second.saved) by assumption();
    have at(statement(6).entry, second.saved) == 42 by assumption();
    have address(second.slot) == address(&first.saved) by assumption();
    have *second.slot == 42 by assumption();
    have first.saved == 42 by assumption();
    step_until(function.exit);
    have *value == 42 by assumption();
}
```

```expect
pass
```
