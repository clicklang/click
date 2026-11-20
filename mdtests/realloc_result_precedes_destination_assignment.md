# Reallocation produces its pointer before assigning it

Even reallocating a null pointer has distinct call and assignment points.
The destination remains null at the call's exit; the assignment then stores
the retained result. The possibly-null allocation result is then returned.

```c filename=resize.c
int32* resize() {
    int32 *p = 0;
    p = realloc(p, 8);
    return p;
}
```

```click
resource allocation_result(p: int32*) {
    if p != 0 {
        owns allocation(p, 8);
    }
}
verifying "resize.c";
int32* resize() {
    produces allocation_result(result);
} by {
    step_until(statement(1).call(0).entry);
    step();
    have at(statement(1).call(0).exit, p == 0) by { known(); }
    step();
    have p == statement(1).call(0).result by { known(); }
    step();
    fold(allocation_result(result));
}
```

```expect
pass
```
