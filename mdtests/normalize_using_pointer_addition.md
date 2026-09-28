# Equal C pointer parameters remain equal under the same displacement

```c filename=pointer_addition.c
void keep(int32* a, int32* b) { }
```

```click
verifying "pointer_addition.c";

void keep(int32* a, int32* b) {
    requires a == b;
    ensures a + 1 == b + 1;
} by {
    execute();
    normalize() using { }
}
```

```expect
pass
```
