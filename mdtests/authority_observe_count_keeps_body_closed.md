# Observing a count does not open the member's memory

```c filename=observe_closed_body.c
int32 probe(int32* p) { return p[0]; }
```

```click resource_semantics=authority
resource permit(p: int32*) { owns p[0..1]; }
verifying "observe_closed_body.c";
int32 probe(int32* p) {
    owns authority(permit(p));
    owns permit(p);
    ensures result == 0;
} by {
    observe(permit(p));
    execute();
    simp();
}
```

```expect
fail: missing resource fact
```
