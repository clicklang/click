# Saved memory requires a pointer base

```c filename=saved_scalar.c
void keep(int p) {}
```

```click
verifying "saved_scalar.c";
void keep(int32 p) { ensures true; } by {
    have contains(memory(old(p)[0..1]), memory(old(p)[0..1])) by { normalize(); }
}
```

```expect
fail: saved memory base must be a pointer
```
