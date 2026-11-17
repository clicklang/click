# Exact conjunction subproofs

Both child proofs inherit the parent assumptions, but not each other's facts.
The nested universal goals retain their own binders.

```click
theorem reflexive_pair(x: int32) {
    ensures x == x and (x <= x and x >= x) by {
        both {
            left => { normalize(); }
            right => {
                both { left => { normalize(); } right => { normalize(); } }
            }
        }
    }
}

theorem quantified_pair() {
    ensures (forall (i: int32) { i == i }) and
            (forall (j: int32) { j <= j }) by {
        both { left => { intro(); normalize(); } right => { intro(); normalize(); } }
    }
}
```

```expect
pass
```
