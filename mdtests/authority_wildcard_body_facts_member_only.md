# Opening a member exposes its invariant without population authority

```c filename=wildcard_body_facts_consumption.c
int32 take(int32* pool, int32* p) { return p[0]; }
```

```click resource_semantics=authority
resource slot(pool: int32*, p: int32*) { owns p[0..1]; fact 0 <= p[0]; }
verifying "wildcard_body_facts_consumption.c";
int32 take(int32* pool, int32* p) {
    owns slot(pool, p);
    ensures 0 <= result;
} by { open(slot(pool, p)) { step(); } simp(); }
```

```expect
pass
```
