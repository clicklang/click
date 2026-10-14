# A predicate packages a precondition

This checks that a predicate can name a memory-reading requirement and that
unfolding it exposes the body as a fact the proof can use.

```c filename=predicate_packages_a_precondition.c
int32 find_zero(int32 p[], int32 n) {
    return 0;
}
```

```click
verifying "predicate_packages_a_precondition.c";

predicate has_zero(p: int32[], n: int32) {
    (0..n).any(|k| { p[k] == 0 })
}

int32 find_zero(int32 p[], int32 n) {
    requires viewable(p[0..n]);
    requires has_zero(p, n);
    ensures body: (0..n).any(|k| { p[k] == 0 }) by {
        execute();
        unfold(has_zero);
        simp();
    }
}
```

```expect
pass
```
