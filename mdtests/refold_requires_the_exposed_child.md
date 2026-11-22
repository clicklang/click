# Moving a child makes the original refold fail

Folding another parent consumes the original child. The open source
parent still names that child by its slot, but cannot reuse its ownership.

```c filename=move_child.c
void move_child(void) {}
```

```click
verifying "move_child.c";

resource leaf() { field tag: int32; }
resource source() { owns child: leaf(); }
resource destination() { owns transferred: leaf(); }

void move_child() {
    owns r: source();
} by {
    unfold(r);
    let holder = fold(destination(), { transferred: r.child });
    fold(r);
}
```

```expect
fail: fold requires an owned, folded child
```
