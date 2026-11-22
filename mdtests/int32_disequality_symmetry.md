# Disequality is symmetric for int32 values

The point-update proof needs the disequality in the opposite operand order
after comparing the marked index with the range endpoint.

```click quick-solve
theorem swap_disequality(x: int32, y: int32) {
    requires x != y;
    ensures y != x by {
        solve() using { x != y; };
    }
}
```

```expect
pass
```
