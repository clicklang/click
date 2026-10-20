# unsupported inferred file-scope array forms remain rejected

Only non-empty initializers infer a scalar array bound; see
`a_file_scope_inferred_array_takes_designators.md` for designated ones. Empty
initializers and aggregate arrays remain outside this slice.

```c filename=invalid.c
int32 empty[] = {};

struct state {
    int32 value;
};

struct state aggregate[] = {{1}};

int32 read() {
    return 0;
}
```

```click
verifying "invalid.c";

int32 read() {
    ensures result == 0 by auto();
}
```

```expect
fail: inferred file-scope array `empty` requires a non-empty initializer
```
