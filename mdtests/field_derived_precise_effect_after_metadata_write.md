# Field-derived precise ownership survives metadata writes

`buffer_push` owns the whole buffer composite, writes only the old end cell,
its successor, and `owner->len`, and promises that the first cell is unchanged
when the old length is positive. The modular caller relies on that promise,
not on the callee's write footprint, to prove that `data[0]` survives the
call: a caller that only views a composite cannot see which of its cells a
callee owned.

```c filename=field_derived_buffer_push.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push(struct buffer* owner, int32 value) {
    int32 index;
    index = owner->len;
    owner->data[index] = value;
    owner->len = index + 1;
    owner->data[index + 1] = 0;
    return index + 1;
}
```

```c filename=field_derived_buffer_push_preserves_first.c
struct buffer {
    int32 len;
    int32 cap;
    int32* data;
};

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    int32 ignored;
    ignored = buffer_push(owner, value);
    return ignored;
}
```

```click
verifying "field_derived_buffer_push.c";
verifying "field_derived_buffer_push_preserves_first.c";

resource owned_buffer(owner: struct buffer*) {
    owns owner->len;
    owns owner->cap;
    owns owner->data;
    owns owner->data[0..owner->cap];
    fact 0 <= owner->len;
    fact owner->len < owner->cap;
    fact separate(
        memory(*owner),
        memory(owner->data[0..owner->cap])
    );
}

int32 buffer_push(struct buffer* owner, int32 value) {
    requires 1 <= owner->len;
    requires to_integer(owner->len + 1) < to_integer(owner->cap);
    owns owned_buffer(owner);

    ensures to_integer(result) == to_integer(old(owner->len) + 1);
    ensures owner->cap == old(owner->cap);
    ensures owner->data == old(owner->data);
    ensures owner->data[0] == old(owner->data[0]);
} by {
    unfold(owned_buffer(owner));
    step_until(function.exit);
    have 0 <= owner->len by {
        solve();
    }
    have owner->len < owner->cap by {
        solve() using {
            to_integer(old(owner->len) + 1) < to_integer(old(owner->cap));
        };
    }
    fold(owned_buffer(owner));
    solve();
}

int32 buffer_push_preserves_first(
    struct buffer* owner,
    int32 data[],
    int32 value
) {
    requires 1 <= owner->len;
    requires to_integer(owner->len + 1) < to_integer(owner->cap);
    requires owner->data == data;
    owns owned_buffer(owner);

    ensures data[0] == old(data[0]);
}
```

```expect
pass
```
