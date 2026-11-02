# Folding an allocation resource requires its arithmetic domain

The requested signed byte count wraps to four, matching the token's bits,
but that does not establish the domain of the resource's size expression.

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
    produces sized_allocation(p, 1073741825);
} by {
    fold(sized_allocation(p, 1073741825));
}
```

```expect
fail: not established: `0 == 1`
```
