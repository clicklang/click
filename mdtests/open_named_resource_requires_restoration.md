# A named resource must close with the fields it had on entry

The body writes a value that contradicts the saved field of the instance.

```c filename=open_named_rejected.c
void set(int32* p) { *p = 8; }
```

```click
verifying "open_named_rejected.c";

resource cell(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}

void set(int32* p) {
    owns c: cell(p);
    requires c.value == 7;
} by {
    with(c) { step_until(function.exit); }
}
```

```expect
fail: body fact
```
