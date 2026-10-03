# Member ownership alone cannot authorize a count observation

```c filename=observe_missing_authority.c
void probe(int32* p) {}
```

```click resource_semantics=authority
resource permit(p: int32*) {}
verifying "observe_missing_authority.c";
void probe(int32* p) {
    owns permit(p);
    ensures 1 <= count(permit(p));
} by {
    observe(permit(p));
    execute();
    simp();
}
```

```expect
fail: count(...) requires owning authority
```
