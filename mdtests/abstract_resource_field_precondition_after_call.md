# A call's precondition on a field an earlier call changed is proved by `auto`

The second `grow` requires `0 <= o.size and o.size <= 1000`, which holds
only through the first call's `ensures o.size == old(o.size) + delta`.
`execute()` records the precondition, spells it at the call's pre-state as
`0 <= o.size and o.size <= 1000`, naming the instance `bump` holds, and
proves it by the implicit `auto`.

```c filename=field_precondition_after_call.c
void grow(int32* self, int32 delta);
void bump(int32* s, int32 delta) { grow(s, delta); grow(s, delta); }
```

```click
verifying "field_precondition_after_call.c";
abstract resource obj(p: int32*) {
    field size: int32;
}
extern void grow(int32* self, int32 delta) {
    owns o: obj(self);
    requires 0 <= delta and delta <= 100;
    requires 0 <= o.size and o.size <= 1000;
    ensures o.size == old(o.size) + delta;
}
void bump(int32* s, int32 delta) {
    owns o: obj(s);
    requires 0 <= delta and delta <= 100;
    requires 0 <= o.size and o.size <= 500;
    ensures o.size == old(o.size) + delta + delta;
} by { execute(); simp(); }
```

```expect
pass
```
