# Repeated requirement facts keep their clause origins

`requires viewable(a[0..n])` and `views a[0..n]` lower to the same entry
fact and the same index-range guards. Entry setup keeps one copy of each
fact, and each kept fact keeps the origin of the first clause that produced
it. The later `forall` requirement is therefore still paired with its own
lowering, not with a guard of the `views` clause.

```c filename=repeated_requirement_facts_keep_their_clause_origins.c
int32 first(int32 a[], int32 n) {
    return a[0];
}
```

```click
verifying "repeated_requirement_facts_keep_their_clause_origins.c";

int32 first(int32 a[], int32 n) {
    requires 1 <= n and n <= 1000;
    requires viewable(a[0..n]);
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies 0 <= a[k]
    };
    ensures result == a[0];
} by {
    step_until(function.exit);
}
```

```expect
pass
```
