# A pre-update truncated result is not the current field

```c filename=old.c
struct state { unsigned long value; };
unsigned int take(struct state *p) {
    unsigned int result = p->value;
    p->value += 1;
    return result;
}
```

```click
verifying "old.c";
unsigned int take(struct state *p) {
    owns p->value;
    ensures result == p->value as uint32;
}
```

```expect
fail: unclosed goal
```
