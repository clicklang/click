# `enumerate` closes instances by evaluation or exact facts

`enumerate()` reads a constant range for each binder from the guard of every
implication leaf, then checks each instance in range order. An instance whose
guard folds to true leaves its conclusion; a conjunction splits; each leaf
either evaluates to true with no facts, as `k * k < 10` does at every `k`, or
is an available fact, as `f(0) == 0` and `f(1) == 1` are here. A guard no
integer satisfies has no instance to check. A `uint64` binder with no stated
lower bound starts at zero.

`enumerate_refuses_an_instance_held_in_another_spelling.md` holds one
instance only as its mirror image.

```click
function f(x: int32) -> int32 { x }

theorem evaluated() {
    ensures forall (k: int32) { 0 <= k and k < 4 implies k * k < 10 } by {
        enumerate();
    }
}

theorem held_instances() {
    requires f(0) == 0;
    requires f(1) == 1;
    ensures forall (k: int32) { 0 <= k and k < 2 implies f(k) == k and k < 2 } by {
        enumerate();
    }
}

theorem empty_range() {
    ensures forall (k: int32) { 0 <= k and k < 0 implies f(k) == 7 } by {
        enumerate();
    }
}

theorem unsigned_from_zero() {
    ensures forall (k: uint64) { k <= 2u64 implies k < 3u64 } by {
        enumerate();
    }
}
```

```expect
pass
```
