# Applying a theorem checks a stated range with its span guards

A theorem that states `views next[0..n]` owes the range and its span guards,
`0 <= n` and `n <= 1073741823`. A caller that states the same range supplies
all three facts.

```c filename=smart_pure_apply_cites_a_range_with_its_span_guards.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "smart_pure_apply_cites_a_range_with_its_span_guards.c";

function walk(next: int32[], from: int32, fuel: Nat) -> int32 decreases fuel {
    match fuel {
        Nat::Zero => from,
        Nat::Succ(previous) => next[walk(next, from, previous)],
    }
}

theorem walk_in_range(next: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views next[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= next[k] and next[k] < n
    };
    ensures 0 <= walk(next, from, fuel) and walk(next, from, fuel) < n by {
        let ih = induct(fuel);
        match fuel {
            Nat::Zero => {
                unfold(walk(next, from, Nat::Zero));
                solve();
            }
            Nat::Succ(previous) => {
                apply(ih(previous));
                have 0 <= next[walk(next, from, previous)]
                    and next[walk(next, from, previous)] < n by {
                    have 0 <= (walk(next, from, previous)) and (walk(next, from, previous)) < n;
                    instantiate(forall (k: int32) {
                        0 <= k and k < n implies 0 <= next[k] and next[k] < n
                    }, walk(next, from, previous));
                    known();
                }
                unfold(walk(next, from, Nat::Succ(previous)));
                known();
            }
        }
    }
}

theorem smart_walk_use(a: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    ensures 0 <= walk(a, from, fuel) by {
        apply(walk_in_range(a, n, from, fuel));
    }
}

theorem explicit_walk_use(a: int32[], n: int32, from: int32, fuel: Nat) {
    requires 0 <= from;
    requires from < n;
    requires n <= 1073741823;
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k] and a[k] < n
    };
    ensures 0 <= walk(a, from, fuel) by {
        apply(walk_in_range(a, n, from, fuel));
    }
}

int32 identity(int32 x) {
    ensures result == x;
}
```

```expect
pass
```
