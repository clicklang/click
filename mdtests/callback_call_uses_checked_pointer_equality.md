# Callback dispatch consumes checked pointer equality directly

```c filename=callbacks.c
struct callbacks { void (*call)(int *p); };
static void target(int *p) { }
static const struct callbacks table = { .call = target };
void concrete(int *p) {
 const struct callbacks *cb = &table;
 cb->call(p);
}
void symbolic(int *p, const struct callbacks *cb) { cb->call(p); }
```

```click
verifying "callbacks.c";
contract void Invoke(int32* p) { ensures true; }
void target(int32* p) { ensures true; } by { execute(); simp(); }
theorem target_has_contract()
executes target(int32* p) {
    ensures Invoke(&target) by { execute(); simp(); }
}
void symbolic(int32* p, const struct callbacks* cb) {
    requires cb == &table;
    views cb->call;
    ensures true;
} by {
    step();
    have cb == &table by { assumption(); }
    step();
    apply(target_has_contract());
    step(Invoke);
    execute(); simp();
}
```

```expect
pass
```
