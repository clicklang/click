# A printed binder does not capture a free name

The goal names the C parameter `k`, free, inside a quantifier whose binder is
also written `k`. A binder prints under its written name only when no free
variable uses it, and otherwise as `k`, `k1`, ..., taking the first name no
free variable uses. Printed as written, the goal would read `forall (k: int32)
{ k == k }`, which reads as true, for a claim that is false.

```c filename=printed_binder_avoids_a_free_name.c
void f(int32* p, int32 k) { }
```

```click
verifying "printed_binder_avoids_a_free_name.c";

resource seg2(p: int32*, n: int32, m: int32) {
    owns p[0..1];
    fact p[0] == n;
    fact m == n;
}

void f(int32* p, int32 k) {
    owns s: seg2(p, k, _);
    requires k == 5;
    ensures forall (k: int32) { k == s.n };
} by {
    execute();
    simp();
}
```

```expect
fail: goal: forall (k1: int32) { k1 == k }
```
