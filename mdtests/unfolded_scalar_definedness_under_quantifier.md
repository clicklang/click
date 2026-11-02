# An unfolded scalar retains its definedness under a quantifier

After a store, the old resource field retains an evaluation obligation even
though its bounds and explicit definedness are known in the current scope.
The unrelated universal binder must not prevent discharging that obligation.

```c filename=unfold_quantifier.c
void check(int32* data) { data[0] = 0; return; }
```

```click
resource bounded(data: int32*) {
    field value: int32;
    owns data[0..10];
    fact 0 <= value;
    fact value < 10;
}
verifying "unfold_quantifier.c";
void check(int32* data) {
    consumes before: bounded(data);
} by {
    let { value: p } = unfold(before);
    step();
    have defined(p + 1) by solve();
    have forall (k: int32) {
        0 <= k and to_integer(k) < to_integer(p + 1) implies data[k] == data[k]
    } by { intro(); intro(); normalize(); }
    step();
}
```

```expect
pass
```
