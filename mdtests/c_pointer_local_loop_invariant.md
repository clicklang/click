# preserve a pointer/index relation across a loop

An explicit invariant can relate a pointer local that is advanced by the loop
to the current array index.

The preservation proof uses the entry pointer relation and the checked
pointer addition theorem. The index bound proves that the increment stays
within the signed integer range.

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
import click::integer;
verifying "c_pointer_local_loop_invariant.c";

int32 last_element(int32 arr[], int32 n, int32 cap) {
    requires 0 <= n;
    requires n < cap;
    requires 1 <= cap;
    requires (cap as uint32) <= 1073741823u32;
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
        maintain by {
            step();
            step();
            have p == arr + i by {
                have p == at(region(5).entry, p) + 1 by close();
                have defined(at(region(5).entry, i) + 1) by {
                    apply(integer::int32_increment_below_max_is_defined(at(region(5).entry, i)));
                    close();
                }
                apply(integer::int32_add_to_integer(at(region(5).entry, i), 1));
                have i == at(region(5).entry, i) + 1 by close();
                apply(integer::int32_pointer_add_associate_int32(arr, at(region(5).entry, i), 1));
                rewrite(p, at(region(5).entry, p) + 1);
                rewrite(at(region(5).entry, p), arr + at(region(5).entry, i));
                rewrite(i, at(region(5).entry, i) + 1);
                close();
            }
        }
    }
    step();
    have result == arr[n] by {
        have at(loop(0).exit, i) == at(loop(0).exit, n);
        rewrite(at(loop(0).exit, p), at(loop(0).exit, arr + i));
        rewrite(at(loop(0).exit, i), at(loop(0).exit, n));
        normalize();
    }
    close();
}
```

```expect
pass
```
