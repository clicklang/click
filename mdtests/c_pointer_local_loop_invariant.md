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

theorem read_same_int32_cell(base: int32*, alias: int32*) {
    requires base == alias;
    requires viewable(memory(*base));
    ensures *alias == *base by {
        rewrite(alias, base);
        close();
    }
}

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
    have i == n by close();
    have p == arr + n by {
        rewrite(p, arr + i);
        rewrite(i, n);
        close();
    }
    mark before_return;
    have viewable(arr[0..cap]) by {
        observe(arr[0..cap]);
    }
    have contains(memory(arr[0..cap]), memory(arr[n])) by {
        apply(click::separation::contains_element(arr, 0, cap, n));
    }
    have viewable(memory(arr[n])) by {
        apply(click::separation::viewable_restrict(memory(arr[0..cap]), memory(arr[n])));
    }
    have *p == arr[n] by {
        apply(read_same_int32_cell(arr + n, p));
        close();
    }
    step();
    have result == at(before_return, *p) by close();
    have result == arr[n] by {
        rewrite(result, at(before_return, *p));
        rewrite(at(before_return, *p), at(before_return, arr[n]));
        close();
    }
    close();
}
```

```expect
pass
```
