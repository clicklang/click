# arithmetic refuses an unsigned step whose premise is not listed

`x - 1 <u x` follows from `0 <u x`, which is a requirement here, but
`arithmetic()` lists no premise and uses exactly what it lists. The goal
stays open, where `simp` would close it from the available fact.

```click
theorem unlisted(x: uint32) {
    requires x > 0u32;
    ensures x - 1u32 < x by arithmetic();
}
```

```expect
fail: current goal does not follow by arithmetic alone; `arithmetic()` without `using` reads no facts from the context
```
