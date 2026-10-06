# preserve a pointer/index relation across a loop

An explicit invariant can relate a pointer local that is advanced by the loop
to the current array index.

The preservation proof names the entry pointer relation and strict index
bound in `arithmetic() using`. The bound excludes index overflow; the checked
step compares exact byte advances, not wrapped int32 offsets. The kernel's
ordinary pointer-equality query need not search ambient facts to find them.

```c filename=c_pointer_local_loop_invariant.c
int32 last_element(int32 arr[], int32 n, int32 cap) {
    int32* p;
    int32 i;
    p = arr;
    i = 0;
    while (i < n) {
        i = i + 1;
        p = p + 1;
    }
    return *p;
}
```

```click
verifying "c_pointer_local_loop_invariant.c";

int32 last_element(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n;
    requires n < cap;
    requires 1 <= cap;
    requires ((uint32)cap) <= 1073741823u32;
    views arr[0..cap];
    ensures result == arr[n];
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0 and i <= n;
        invariant p == arr + i;
        preserve by {
            step();
            step();
            have p == arr + i by {
                arithmetic() using {
                    at(statement(5).entry, p) == at(statement(5).entry, arr + i);
                    at(statement(5).entry, i) < at(statement(5).entry, n);
                }
            }
            close_invariants by { simp(); }
        }
    }
    step();
    have result == arr[n] by {
        have at(loop(0).exit, i) == at(loop(0).exit, n) by {
            apply(int32_le_and_not_lt_implies_eq(at(loop(0).exit, i), at(loop(0).exit, n))) using {
                at(loop(0).exit, i) <= at(loop(0).exit, n);
                not at(loop(0).exit, i) < at(loop(0).exit, n);
            }
        }
        rewrite(at(loop(0).exit, p) == at(loop(0).exit, arr + i));
        rewrite(at(loop(0).exit, i) == at(loop(0).exit, n));
        normalize();
    }
    assumption();
}
```

```expect
pass
```
