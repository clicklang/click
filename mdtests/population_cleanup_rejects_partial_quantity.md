# Cleanup requires the requested quantity to be the whole population

```c filename=partial_cleanup.c
struct counter { unsigned int value; };
unsigned int cleanup(struct counter* p) { p->value = 0u; return p->value; }
```

```click
verifying "partial_cleanup.c";
resource remaining(p: struct counter*) {
    owns p->value;
    fact p->value == 3 - count(remaining(p));
}
uint32 cleanup(struct counter* p) {
    owns p->value;
} by {
    step();
    fold(3 of remaining(p));
    unfold(2 of remaining(p));
    step();
    simp();
}
```

```expect
fail: Requires count(remaining(p)) == 2
```
