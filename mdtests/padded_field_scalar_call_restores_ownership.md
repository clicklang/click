# A scalar call restores ownership of a padded field

The final signed-32 field occupies an eight-byte ownership slot because the
struct has eight-byte alignment. Calling a helper on its address lends the
four scalar bytes and preserves the padding. The returned scalar bytes and
preserved padding rejoin through their exact byte endpoints, including when
the object pointer is symbolic. The adjacent signed-64 field stays framed.

```c filename=padded_field_scalar_call.c
struct State {
    int64 fee;
    int32 size;
};

void bump(int32* value) {
    *value = *value + 1;
}

void caller(struct State* state) {
    bump(&state->size);
}
```

```click
verifying "padded_field_scalar_call.c";

void bump(int32* value) {
    owns value[0..1];
    requires 0 <= value[0];
    requires value[0] <= 10;
    ensures value[0] == old(value[0]) + 1;
} by { execute(); simp(); }

void caller(struct State* state) {
    owns state->size;
    views state->fee;
    requires 0 <= state->size;
    requires state->size <= 10;
    ensures state->size == old(state->size) + 1;
    ensures state->fee == old(state->fee);
} by { execute(); simp(); }
```

```expect
pass
```
