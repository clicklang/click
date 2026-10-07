# Observed symbolic custody does not assert an exact total

```c filename=observe_symbolic_total.c
void probe(int32* p, int32 amount) {}
```

```click resource_semantics=authority
authorized resource permit(p: int32*) {}
verifying "observe_symbolic_total.c";
void probe(int32* p, int32 amount) {
    requires 0 <= amount;
    owns authority(permit(p));
    owns amount of permit(p);
    ensures count(permit(p)) == amount;
} by {
    observe(amount of permit(p));
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
