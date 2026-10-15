# A `by` after an `open` whose close leaves nothing open is refused

The body fact holds exactly after the store, so the closing fold leaves no
body fact open and the `by` proves nothing.

```c filename=open_by_superfluous.c
void set(int32* p, int32 x) { p[0] = x; }
```

```click
resource cell(p: int32*) { owns p[0..1]; fact p[0] > 0; }
verifying "open_by_superfluous.c";
void set(int32* p, int32 x) {
    requires x > 0;
    owns cell(p);
} by {
    open(cell(p)) { execute(); } by { simp(); }
    simp();
}
```

```expect
fail: the `by` after `open` is superfluous
```
