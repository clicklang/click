# A loop walking a member array stays in it

The pointer walks `r->arr` one element per iteration. Across the abstract
iteration it keeps designating the member array, so its four stores are
checked against the array, and they stay inside it.

```c filename=walk.c
struct Rec { int32 arr[4]; int32 tail; };
int32 walk(struct Rec* r, int32 n) {
    int32* p;
    int32 i;
    p = r->arr;
    i = 0;
    while (i < n) {
        *p = 0;
        i = i + 1;
        p = p + 1;
    }
    return 0;
}
```

```click
import click::integer;
verifying "walk.c";
int32 walk(struct Rec* r, int32 n) {
    requires 0 <= n;
    requires n <= 4;
    owns r->arr[0..4];
    owns r->tail;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0 and i <= n;
        invariant p == &r->arr[0] + i;
        maintain by {
            step();
            step();
            step();
            have p == &r->arr[0] + i by {
                have p == at(region(5).entry, p) + 1 by known();
                have defined(at(region(5).entry, i) + 1) by {
                    apply(integer::int32_increment_below_max_is_defined(at(region(5).entry, i)));
                    known();
                }
                apply(integer::int32_add_to_integer(at(region(5).entry, i), 1));
                have i == at(region(5).entry, i) + 1 by known();
                apply(integer::int32_pointer_add_associate_int32((&r->arr[0] as (int32 *)), at(region(5).entry, i), 1));
                rewrite(p, at(region(5).entry, p) + 1);
                rewrite(at(region(5).entry, p), &r->arr[0] + at(region(5).entry, i));
                rewrite(i, at(region(5).entry, i) + 1);
                known();
            }
        }
    }
}
```

```expect
pass
```
