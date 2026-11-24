# uint8 pure function in a loop invariant

This checks that loop-invariant spec lowering preserves the element type for
pure Click functions over `uint8[]` array refs. The loop writes only the tail,
so the first byte remains equal to its entry-state value.

The back-edge proof uses the store footprint to carry the first byte
across the write, then re-establishes the pure-function invariant.

```c filename=uint8_loop_invariant_pure_function.c
uint8 fill_byte_tail(uint8 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = 'z';
        i = i + 1;
    }
    return p[0];
}
```

```click
verifying "uint8_loop_invariant_pure_function.c";

function first_byte(p: uint8[]) -> uint8 {
    p[0]
}

uint8 fill_byte_tail(uint8 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires viewable(p[0..n]);
    consumes p[0..n];
    ensures first_preserved: result == old(first_byte(p));
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 1 and i <= n;
        invariant first_byte(p) == old(first_byte(p));
        maintain by {
            mark before_store;
            unfold(first_byte(p));
            have p[0] == old(first_byte(p)) by { close(); }
            have i != 0 by { close() using { i >= 1; }; }
            apply(click::separation::separate_elements(p, i, 0));
            step();
            have separate(loop(0).statement(0).footprint, memory(p[0])) by {
                normalize() using { at(before_store, separate(memory(p[i]), memory(p[0]))); };
            }
            have p[0] == at(before_store, p[0]) by {
                preserve(memory(p[0]), loop(0).statement(0));
            }
            have p[0] == old(first_byte(p)) by {
                rewrite(p[0], at(before_store, p[0]));
                close();
            }
            step();
            have first_byte(p) == p[0] by { unfold(first_byte(p)); close(); }
            have first_byte(p) == old(first_byte(p)) by {
                rewrite(first_byte(p), p[0]);
                close();
            }
            close();
        }
        otherwise {
            have first_byte(p) == p[0] by { unfold(first_byte(p)); close(); }
            have p[0] == old(first_byte(p)) by {
                rewrite(p[0], first_byte(p));
                close();
            }
        }
    }
    step();
    close();
}
```

```expect
pass
```
