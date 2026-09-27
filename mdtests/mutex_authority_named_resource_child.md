# Named primitive children have an explicit implementation boundary

```click
resource holding(mu: void*) {
    field tag: int32;
    owns guard: mutex_guard(mu);
}
```

```expect
fail: named mutex_guard is currently supported only in preserving C function contracts
```
