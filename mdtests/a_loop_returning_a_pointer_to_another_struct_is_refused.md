# A loop returning a pointer to another struct is refused

A loop keeps the class of the object a pointer local designates across the
abstract iteration. A back edge that leaves `pa` designating a `struct b`
changes that class, so the loop-head state checked against `struct a` does
not cover it and the join is refused. A back edge that returns the pointer
unclassed keeps the head's class
(`a_loop_may_return_a_struct_pointer_unclassed_from_its_tag_bits.md`).

```c filename=other.c
struct a { int x; };
struct b { int y; };

int swap_in(struct a *pa, struct b *pb, int n) {
    void *v = pb;
    while (n != 0) {
        pa = v;
        n = n - 1;
    }
    return n;
}
```

```click
verifying "other.c";

int32 swap_in(struct a *pa, struct b *pb, int32 n) {
    requires n >= 0;
    requires n <= 10;
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases n;
        invariant n >= 0;
        invariant n <= 10;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: loop state join changes pointer object classes
```
