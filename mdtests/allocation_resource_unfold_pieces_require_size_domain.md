# Matching allocation pieces do not supply an unfold domain

The canonical already-unfolded path may reuse exposed pieces, but it cannot
assume a missing head's arithmetic domain merely because its size wraps to
that of a held token.

```c filename=allocation_size_domain.c
void pack(int32 *p) {}
```

```click
resource sized_allocation(p: int32*, count: int32) {
    owns allocation(p, count * 4);
}

verifying "allocation_size_domain.c";
void pack(int32* p) {
    owns allocation(p, 4);
} by {
    unfold(sized_allocation(p, 1073741825));
}
```

```expect
fail: not established: `not to_integer(0) == 0`
```
