# A larger cell is not contained in a smaller one

```click
theorem wider(p: int32*) {
    ensures contains(memory(p[0..1]), memory(((p as (void *)) as (uint64 *))[0..1])) by { normalize(); }
}
```

```expect
fail: did not normalize to true
```
