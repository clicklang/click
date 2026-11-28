# A scope started at return must restore the original fields

The explicit fold puts back an instance with a different field value.

```c filename=with_at_return_requires_original_fields.c
void keep(int32* p) {}
```

```click
verifying "with_at_return_requires_original_fields.c";

resource cell(p: int32*) {
    field tag: int32;
    owns *p;
}

void keep(int32* p) {
    owns c: cell(p);
    requires c.tag == 7;
} by {
    step_until(function.exit);
    with(c) {
        let c = fold(cell(p), { tag: 8 });
    }
    close();
}
```

```expect
fail: fold result identity is already in use
```
