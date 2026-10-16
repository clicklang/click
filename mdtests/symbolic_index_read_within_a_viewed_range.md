# A symbolic index read inside a viewed range

This checks that a read at a symbolic index `p[k]` verifies when the contract
states both the viewable range and the index bounds `0 <= k` and `k < n`.

```c filename=symbolic_index_read_within_a_viewed_range.c
int32 element_at(int32 p[], int32 k, int32 n) {
    return p[k];
}
```

```click
verifying "symbolic_index_read_within_a_viewed_range.c";

int32 element_at(int32 p[], int32 k, int32 n) {
    requires 0 <= k;
    requires k < n;
    requires viewable(p[0..n]);
    views p[0..n];
    ensures result == p[k] by auto();
}
```

```expect
pass
```
