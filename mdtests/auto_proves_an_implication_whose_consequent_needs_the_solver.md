# `auto` proves an implication whose consequent needs the solver

Under `arithmetic "integer";`, `b->cap == old(b->cap) + 1` compares exact
Integers, so proving it needs the operation identity
`to_integer(old(b->cap) + 1) == to_integer(old(b->cap)) + 1`, which only the
solver finds. As a claim under `result == 1 implies`, the antecedent reads
`true` on the growing path and `simp` misses the consequent. `auto` then
introduces the antecedent and runs the solver on the consequent. The function
shape is the owned-vector example's `vector_grow`.

```c filename=grow_box.c
struct box { int cap; };

int grow(struct box *b) {
    if (b->cap >= 1000) {
        return 0;
    }
    b->cap = b->cap + 1;
    return 1;
}
```

```click
arithmetic "integer";
verifying "grow_box.c";

int32 grow(struct box* b) {
    requires 0 <= b->cap;
    owns *b;
    ensures result == 0 or result == 1;
    ensures result == 1 implies b->cap == old(b->cap) + 1;
}
```

```expect
pass
```
