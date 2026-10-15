# A member pointer cannot be passed as a longer range

A memory clause names its range through a pointer, so it claims the pointer
designates that range. `&p->first` designates one `int32`; passing it where
the callee views `p[0..2]` would let the callee read `second` through it,
although the caller owns both members. The call is refused.

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 arr(int32* p) { return p[1]; }
int32 caller(struct Pair* p) { return arr(&p->first); }
```

```click
verifying "probe.c";
int32 arr(int32* p) {
    views p[0..2];
    ensures result == p[1];
} by { execute(); simp(); }
int32 caller(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

```expect
fail: memory range leaves the pointer's selected object domain
```
