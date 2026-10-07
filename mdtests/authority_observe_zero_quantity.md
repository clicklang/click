# Observing zero quantity exposes no member body

The authority permits observing the arbitrary total. A zero coefficient grants
no memory or member custody.

```c filename=observe_zero_quantity.c
void probe(int32* p) {}
```

```click resource_semantics=authority
authorized resource permit(p: int32*) {}
verifying "observe_zero_quantity.c";
void probe(int32* p) {
    owns authority(permit(p));
    owns 0 of permit(p);
    ensures 0 <= count(permit(p));
} by {
    observe(0 of permit(p));
    execute();
    simp();
}
```

```expect
pass
```
