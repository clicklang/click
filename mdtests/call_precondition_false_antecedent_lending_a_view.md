# A call precondition whose antecedent the arguments decide false is discharged

`window` lends `p[0..1]` as a view and requires
`n != 7u64 implies n <= k`, the shape of `std::span::subspan`'s count
requirement with `std::dynamic_extent` as the sentinel. `use_all` passes the
sentinel, so the antecedent is `7u64 != 7u64` and the requirement holds
without any fact about `k`. A call that lends a view refuses to recover it
while a precondition is pending, so the probe retains the trivially true
clause, the implicit `auto` proves it at the pre-state, and the call is
retried with that evidence. `call_precondition_true_antecedent_false_consequent`
is the refusal when the antecedent holds.

```c filename=window.c
int32 window(int32* p, uint64 k, uint64 n) {
    return p[0];
}

int32 use_all(int32* p, uint64 k) {
    return window(p, k, 7);
}
```

```click
verifying "window.c";

int32 window(int32* p, uint64 k, uint64 n) {
    views p[0..1];
    requires n != 7u64 implies n <= k;
    ensures result == old(p[0]);
} by { execute(); simp(); }

int32 use_all(int32* p, uint64 k) {
    views p[0..1];
    ensures result == old(p[0]);
} by { execute(); simp(); }
```

```expect
pass
```
