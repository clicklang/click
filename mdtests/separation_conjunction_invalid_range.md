# A conjunction can name a reversed logical range

```click
theorem invalid(p: int32*, A: Resource) {
    requires separate(memory(p[2..1]) * A, A);
    ensures true;
}
```

```expect
pass
```
