# Instantiate a wide memory invariant with a computed bound

A held universal remains available when its machine comparison is represented
by a shared Integer observation and its body reads memory.

```c filename=instantiate_a_wide_memory_invariant_with_a_computed_bound.c
void f(int *p, unsigned long end, unsigned long count, unsigned long k) {
    unsigned long start = end - count;
    while (k < start) {
        k++;
    }
}
```

```click
verifying "instantiate_a_wide_memory_invariant_with_a_computed_bound.c";
void f(int32* p, uint64 end, uint64 count, uint64 k) {
    views p[0..end];
    ensures end == old(end);
    requires count <= end;
} by {
    step_until(loop(0).entry);
    loop {
        decreases to_integer(start) - to_integer(k);
        invariant forall (j: uint64) { j < start implies p[j] == old(p[j]) };
        initialize by {
            have forall (j: uint64) { j < start implies p[j] == old(p[j]) } by {
                intro(); intro(); known();
            }
        }
        maintain by {
            have forall (x: uint64) { x < start implies p[x] == old(p[x]) } by {
                intro(); intro();
                instantiate(forall (j: uint64) { j < start implies p[j] == old(p[j]) }, x);
                known();
            }
            step();
        }
    }
}
```

```expect
pass
```
