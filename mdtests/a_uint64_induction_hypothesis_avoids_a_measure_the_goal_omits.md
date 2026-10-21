# A uint64 induction hypothesis avoids a measure the goal omits

When neither the goal nor a requirement mentions the `uint64` measure `n`,
the hypothesis still binds a variable distinct from `n`, guarded by
`m < n`, so `ih` applies at `n - 1u64` in both the `using` form and the
bare form.

```c filename=a_uint64_induction_hypothesis_avoids_a_measure_the_goal_omits.c
void unused(void) {}
```

```click
verifying "a_uint64_induction_hypothesis_avoids_a_measure_the_goal_omits.c";

function k(x: uint64) -> uint64 { x }

theorem with_using(n: uint64) {
    ensures k(3u64) == 3u64 by {
        induct(n) as ih;
        if n <= 0u64 {
            unfold(k(3u64));
            normalize();
        } else {
            have 0u64 < n by simp();
            have n - 1u64 < n by arithmetic() using { 0u64 < n; };
            apply(ih(n - 1u64)) using { n - 1u64 < n; };
        }
    }
}

theorem bare(n: uint64) {
    ensures k(3u64) == 3u64 by {
        induct(n) as ih;
        if n <= 0u64 {
            unfold(k(3u64));
            normalize();
        } else {
            have 0u64 < n by simp();
            have n - 1u64 < n by arithmetic() using { 0u64 < n; };
            apply(ih(n - 1u64));
        }
    }
}
```

```expect
pass
```
