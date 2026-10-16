# A callee's `ensures` about an abstract resource's field supports arithmetic

`grow`'s `ensures o.size == old(o.size) + delta` relates the new field to the
old one. Through two calls, `simp` substitutes the equalities in turn: the
caller states the size two steps on, bounds it, and reads it back as an
offset from entry, none of which restates `grow`'s postcondition.

```c filename=abstract_resource_field_call_facts_support_arithmetic.c
void grow(int32* self, int32 delta);
void bump(int32* s) { grow(s, 1); grow(s, 1); }
```

```click
verifying "abstract_resource_field_call_facts_support_arithmetic.c";
abstract resource obj(p: int32*) {
    field size: int32;
}
extern void grow(int32* self, int32 delta) {
    owns o: obj(self);
    requires 0 <= delta and delta <= 100;
    requires 0 <= o.size and o.size <= 1000;
    ensures o.size == old(o.size) + delta;
}
void bump(int32* s) {
    owns o: obj(s);
    requires 0 <= o.size and o.size <= 500;
    ensures o.size == old(o.size) + 2;
    ensures o.size - 2 == old(o.size);
    ensures o.size <= 502;
} by { execute(); simp(); }
```

```expect
pass
```
