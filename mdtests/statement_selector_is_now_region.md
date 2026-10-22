# `statement(N)` is now `region(N)`

A program point once named the `N`th lowered statement `statement(N)`. That
count includes each call a C statement makes as a region of its own, so it is
now `region(N)`, and `statement` is reserved for a statement as written. The
old spelling is refused with the new one named, rather than read as something
else.

```c filename=region_rename.c
void set(int32* p) {
    *p = 1;
}
```

```click
verifying "region_rename.c";

void set(int32* p) {
    owns p[0..1];
    ensures p[0] == 1;
} by {
    step();
    have at(statement(0).exit, p[0]) == 1;
    execute();
    simp();
}
```

```expect
fail: `statement(N)` is now `region(N)`
```
