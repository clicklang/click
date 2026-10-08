# Built-in object ownership composes inside a population member

```c filename=contained_object.c
struct payload { int32 value; };
int32 update(int32* pool, struct payload* p) { p->value = 7; return 7; }
```

```click resource_semantics=authority
resource slot(pool: int32*, p: struct payload*) { owns *p; }
verifying "contained_object.c";
int32 update(int32* pool, struct payload* p) {
    owns slot(pool, p);
    ensures result == 7;
    ensures p->value == 7;
} by { open(slot(pool, p)) { step(); } execute(); simp(); }
```

```expect
pass
```
