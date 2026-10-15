# A call precondition whose antecedent holds still owes its consequent

The callee of `call_precondition_false_antecedent_lending_a_view`, called
with `n == 5u64` and `k == 3u64`. The antecedent `5u64 != 7u64` holds, so the
requirement is `5u64 <= 3u64`, which is false. Discharging an implication
with a false antecedent must not discharge this one.

```c filename=window.c
int32 window(int32* p, uint64 k, uint64 n) {
    return p[0];
}

int32 use_five(int32* p) {
    return window(p, 3, 5);
}
```

```click
verifying "window.c";

int32 window(int32* p, uint64 k, uint64 n) {
    views p[0..1];
    requires n != 7u64 implies n <= k;
    ensures result == old(p[0]);
} by { execute(); simp(); }

int32 use_five(int32* p) {
    views p[0..1];
    ensures result == old(p[0]);
} by { execute(); simp(); }
```

```expect
fail: precondition clause 2 of `window`
```
