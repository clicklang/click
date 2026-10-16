# Two calls' `ensures` about one cell support arithmetic

After two calls to `grow`, the cell's middle value is readable only at the
second call's entry. `simp` substitutes both calls' equalities to read the
final value as an offset from entry.

```c filename=two_call_memory_facts_support_arithmetic.c
void grow(int32* self, int32 delta);
void bump(int32* s) { grow(s, 1); grow(s, 1); }
```

```click
verifying "two_call_memory_facts_support_arithmetic.c";
extern void grow(int32* self, int32 delta) {
    owns self[0..1];
    requires 0 <= delta and delta <= 100;
    requires 0 <= self[0] and self[0] <= 1000;
    ensures self[0] == old(self[0]) + delta;
}
void bump(int32* s) {
    owns s[0..1];
    requires 0 <= s[0] and s[0] <= 500;
    ensures s[0] - 2 == old(s[0]);
} by { execute(); simp(); }
```

```expect
pass
```
