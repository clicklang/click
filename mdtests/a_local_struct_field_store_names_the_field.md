# A memory-history refusal names the local struct field a loop writes

The loop writes `s.b` through `p`, four bytes at offset 4 of the local `s`.
The local's declaration carries `struct pair`'s layout, and exactly one of
its fields occupies exactly those bytes, so the refusal names the field,
`s.b`, in the memory-history sentence and in the goal, instead of `s+4` and
`*(int32 *)((char *)&s + 4)`.

```c filename=a_local_struct_field_store_names_the_field.c
struct pair {
    int32 a;
    int32 b;
};

int32 loop_writes_field() {
    struct pair s;
    int32* p;
    int32 i;
    s.a = 1;
    s.b = 3;
    p = &s.b;
    i = 0;
    while (i < 2) {
        p[0] = 9;
        i = i + 1;
    }
    return s.b;
}
```

```click
verifying "a_local_struct_field_store_names_the_field.c";

int32 loop_writes_field() {
    ensures result == 3;
} by {
    execute_until(loop(0));
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
fail: left side evaluated to at(<state A>, s.b), right side evaluated to 3; `s.b` may have changed since earlier in this function
```
