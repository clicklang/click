# A named resource scope can start at function exit

The returned state still owns the same outer resource. The nested scope
exposes its child, and each scope restores the instance it opened.

```c filename=with_starts_at_return.c
int32 read_tag(void) { return 0; }
```

```click
verifying "with_starts_at_return.c";

resource leaf() { field tag: int32; }
resource inner() { owns item: leaf(); }
resource outer() { owns child: inner(); }

int32 read_tag() {
    owns r: outer();
    ensures r.child.item.tag == old(r.child.item.tag);
} by {
    step_until(function.exit);
    with(r) {
        with(r.child) {
            if result == 0 {
                have r.child.item.tag == old(r.child.item.tag) by close();
            } else {}
        }
    }
    close();
}
```

```expect
pass
```
