# A conjunction does not hide an invalid memory extent

```click
theorem invalid(p: int32*, A: Resource) {
    requires separate(memory(p[2..1]) * A, A);
    ensures true;
}
```

```expect
fail: range
```
