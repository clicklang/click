# Symbolic resource quantities retain their implicit entry guard

An `owns n of slot(pool)` clause already requires `n >= 0` at a call and
permits a callee to assume that condition at entry. The proof context must
retain the condition used during resource setup: checking the function entry
again must neither demand a redundant explicit requirement nor crash.

```c filename=symbolic_quantity.c
void inspect(int32* pool, int32 n) {}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*) {}
verifying "symbolic_quantity.c";
void inspect(int32* pool, int32 n) {
    owns authority(slot(pool));
    owns n of slot(pool);
    ensures 0 <= n;
} by {
    execute(); simp();
}
```

```expect
pass
```
