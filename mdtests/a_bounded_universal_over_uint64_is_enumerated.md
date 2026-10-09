# A bounded universal over uint64 is enumerated

A universal whose binder is bounded by comparisons with constants has a
finite domain, and `simp` closes it by checking each member. The domain
was read from signed 32-bit bounds only, so at a function's exit the same
claim over a `uint64` binder was left open, although a pure theorem proved
it.

`empty` has no member: `k < 0u64` is false for every unsigned value, which
is what the guard folds to. `small` has three members, from zero, since an
unsigned binder with no stated lower bound starts there. `window` states
both bounds.

`a_false_bounded_universal_over_uint64_is_refused.md` claims something one
member does not satisfy.

```c filename=a_bounded_universal_over_uint64_is_enumerated.c
void nop(unsigned long length) { }
```

```click
verifying "a_bounded_universal_over_uint64_is_enumerated.c";

void nop(uint64 length) {
    ensures empty: forall (k: uint64) { k < 0u64 implies k == 5u64 };
    ensures small: forall (k: uint64) { k < 3u64 implies k <= 2u64 };
    ensures window: forall (k: uint64) { 2u64 <= k and k < 3u64 implies k == 2u64 };
} by { execute(); simp(); }
```

```expect
pass
```
