# A loop walking past a member array is refused

The pointer walks `r->arr` one element per iteration. Across the abstract
iteration it keeps designating the member array, so the fifth store, at the
address of `r->tail`, is refused although the contract owns `r->tail`.

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
import click::machine_integer;
verifying "walk.c";
int32 walk(struct Rec* r, int32 n) {
    requires 0 <= n;
    requires n <= 5;
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
        preserve by {
            step();
            step();
            step();
            have p == &r->arr[0] + i by {
                arithmetic() using {
                    at(statement(5).entry, p) == at(statement(5).entry, &r->arr[0] + i);
                    at(statement(5).entry, i) < at(statement(5).entry, n);
                }
            }
            close_invariants by simp();
        }
    }
    execute();
    simp();
}
```

```expect
fail: access outside the subobject the pointer designates
```
