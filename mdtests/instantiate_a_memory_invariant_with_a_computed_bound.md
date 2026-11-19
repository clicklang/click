# Instantiate a memory invariant with a computed bound

A held universal remains available when its machine comparison is represented
by a shared Integer observation and its body reads memory.

```c filename=instantiate_a_memory_invariant_with_a_computed_bound.c
void f(int *p, int end, int count, int k) {
    int start = end - count;
    while (k < start) {
        k++;
    }
}
```

```click
verifying "instantiate_a_memory_invariant_with_a_computed_bound.c";
void f(int32* p, int32 end, int32 count, int32 k) {
    views p[0..end];
    ensures end == old(end);
    requires 0 <= count;
    requires count <= end;
} by {
    step_until(loop(0));
    loop {
        decreases to_integer(start) - to_integer(k);
        invariant forall (j: int32) { 0 <= j and j < start implies p[j] == old(p[j]) };
        initialize by {
            have forall (j: int32) { 0 <= j and j < start implies p[j] == old(p[j]) } by {
                intro(); intro(); normalize();
            }
        }
        maintain by {
            have forall (x: int32) { 0 <= x and x < start implies p[x] == old(p[x]) } by {
                intro(); intro();
                instantiate(forall (j: int32) { 0 <= j and j < start implies p[j] == old(p[j]) }, x);
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
