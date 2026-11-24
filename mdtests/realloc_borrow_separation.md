# A disjoint view survives both realloc outcomes

The proof separates the complete old allocation from the view before the
resize. The success branch uses that separation to retire the old allocation.
The failure branch returns the original allocation.

```c filename=resize_borrow.c
unsigned char *resize(int32 *q) {
    unsigned char *p = malloc(16);
    if (p == 0) {
        return 0;
    }
    unsigned char *next = realloc(p, 16);
    if (next == 0) {
        return p;
    }
    return next;
}
```

```click
verifying "resize_borrow.c";

resource resized(p: uint8*) {
    if p != 0 {
        owns allocation(p, 16);
    }
}

uint8* resize(int32* q) {
    views *q;
    produces resized(result);
} by {
    step();
    step();
    branch {
        true => {
            step();
            fold(resized(result));
            close();
        }
        false => {}
    }
    have separate(memory(p[0..16]), memory(*q)) by { close(); }
    step();
    step();
    step();
    branch {
        true => {
            step();
            fold(resized(result));
            close();
        }
        false => {}
    }
    step();
    fold(resized(result));
}
```

```expect
pass
```
