# A returned allocation at the same pointer cannot change size

Returning the original pointer does not authorize inventing a larger allocation.
The unchanged callee cannot produce an eight-byte token from a four-byte one.

```c filename=pass_through.c
int *pass(int *p) { return p; }
```

```click
verifying "pass_through.c";
int32* pass(int32* p) {
    consumes allocation(p, 4);
    ensures result == p;
    produces allocation(result, 8);
}
```

```expect
fail: missing resource fact `owns allocation(p, 8)`
```
