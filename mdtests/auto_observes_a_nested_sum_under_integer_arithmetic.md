# `auto` observes a nested sum under Integer arithmetic

Under `arithmetic "integer";`, `result == a + b + c` compares
`to_integer(result)` with `to_integer(a) + to_integer(b) + to_integer(c)`. The
returned value is the machine sum `(a + b) + c`, so `auto` needs two operation
identities, and the outer one's range bounds need the inner one. `auto` proves
the inner identity first, so the outer bounds read it and no proof states it.
The function shape is the binary-tree example's `tree_sum_root_and_children`:
the inner sum is stored in a local and its operands are memory reads.

```c filename=sum_three.c
int sum_params(int a, int b, int c) {
    int s;
    s = a + b;
    return s + c;
}

int sum_reads(int *p) {
    int s;
    s = p[0] + p[1];
    return s + p[2];
}
```

```click
arithmetic "integer";
verifying "sum_three.c";

int32 sum_params(int32 a, int32 b, int32 c) {
    requires 0 <= a;
    requires a <= 1000;
    requires 0 <= b;
    requires b <= 1000;
    requires 0 <= c;
    requires c <= 1000;
    ensures result == a + b + c;
}

int32 sum_reads(int32 *p) {
    views p[0..3];
    requires 0 <= p[0];
    requires p[0] <= 1000;
    requires 0 <= p[1];
    requires p[1] <= 1000;
    requires 0 <= p[2];
    requires p[2] <= 1000;
    ensures result == p[0] + p[1] + p[2];
}
```

```expect
pass
```
