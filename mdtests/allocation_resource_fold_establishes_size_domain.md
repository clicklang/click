# A defined allocation size can be folded

```c filename=allocation_size_domain.c
void pack(int32 *p) {}
```

```click
resource sized_allocation(p: int32*, count: int32) {
    owns allocation(p, count * 4);
}

verifying "allocation_size_domain.c";
void pack(int32* p) {
    consumes allocation(p, 4);
    produces sized_allocation(p, 1);
} by {
    fold(sized_allocation(p, 1));
}
```

```expect
pass
```
