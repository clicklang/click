# intro as names a range quantifier's variable

A range quantifier keeps its variable in the lambda, `(lo..hi).all(|k| { ...
})`. `intro() as name` renames it as it renames a `forall` binder: the
variable is `i` from here on, the next `intro()` introduces the range guard,
and a later step reads the variable under its new name. The same holds for a
`forall` over a `spec enum` type.

```click
spec enum Shade { Dark, Light }

theorem range_goal(n: int32) {
    ensures (0..n).all(|k| { k == k }) by {
        intro() as i;
        intro();
        normalize();
    }
}

theorem range_variable_is_read_under_its_new_name(n: int32) {
    ensures (0..n).all(|k| { k < n }) by {
        intro() as i;
        intro();
        have i < n by assumption();
        assumption();
    }
}

theorem enum_binder() {
    ensures forall (s: Shade) { s == s } by {
        intro() as t;
        have t == t by simp;
        simp();
    }
}
```

```expect
pass
```
