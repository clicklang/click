# Named intro names a range quantifier's variable

A range quantifier keeps its variable in the lambda, `(lo..hi).all(|k| { ...
})`. The block `intro(i) { ... }` binds it as `i` and brings the bounds into
scope. A named introduction also works for a `forall` over a `spec enum`
type.

```click
spec enum Shade { Dark, Light }

theorem range_goal(n: int32) {
    ensures (0..n).all(|k| { k == k }) by {
        intro(i) {
            close();
        }
    }
}

theorem range_variable_is_read_under_its_new_name(n: int32) {
    ensures (0..n).all(|k| { k < n }) by {
        intro(i) {
            have i < n by close();
            close();
        }
    }
}

theorem enum_binder() {
    ensures forall (s: Shade) { s == s } by {
        intro(t) {
            have t == t by close();
            close();
        }
    }
}
```

```expect
pass
```
