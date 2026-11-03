# Expose separation after unfolding a named owner beside a view

```c filename=probe.c
void check(int32* p, int32* q) {}
```

```click
resource owner(p: int32*) {
    field unused: int32;
    owns p[0..1];
}
verifying "probe.c";
void check(int32* p, int32* q) {
    views q[0..1];
    consumes r: owner(p);
} by {
    let { unused: m } = unfold(r);
    have separate(memory(p[0..1]), memory(q[0..1])) by { solve(); }
    step_until(function.exit);
}
```

```expect
pass
```
