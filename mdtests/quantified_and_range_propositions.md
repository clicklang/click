# Quantified and range propositions in a contract

This checks that `forall`, `exists`, and the range forms `(0..n).all` and
`(0..n).any` can state facts about a viewed array in requirements and
guarantees.

```c filename=quantified_and_range_propositions.c
int32 keep(int32 p[], int32 n, int32 value) {
    return 0;
}
```

```click
verifying "quantified_and_range_propositions.c";

int32 keep(int32 p[], int32 n, int32 value) {
    views p[0..n];
    requires exists (k: int32) {
        0 <= k and k < n and p[k] == value
    };
    requires (0..n).all(|k| {
        p[k] == 0
    });
    requires (0..n).any(|k| {
        p[k] == value
    });
    ensures unchanged: forall (k: int32) {
        0 <= k and k < n implies p[k] == old(p[k])
    } by auto;
    ensures still_zero: (0..n).all(|k| { p[k] == 0 }) by auto;
    ensures still_found: (0..n).any(|k| { p[k] == value }) by auto;
}
```

```expect
pass
```
