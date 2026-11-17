# unfolding selects explicit predicate applications

Each application is opened independently. A later `have` needs its own unfold.

```click
predicate small(x: int32) { 0 <= x and x <= 5 }

theorem unfold_selected_applications(a: int32, b: int32, c: int32) {
    requires small(a);
    requires small(b);
    requires 0 <= c;
    requires c <= 5;
    ensures 0 <= a and 0 <= b by {
        unfold(small(a));
        unfold(small(b));
        have small(c) by { unfold(small(c)); known(); }
        known();
    }
}
```

```expect
pass
```
