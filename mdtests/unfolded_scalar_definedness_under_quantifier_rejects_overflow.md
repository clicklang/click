# A quantified unfolded scalar still requires defined arithmetic

A free scalar without an upper bound can overflow even under an unrelated
universal binder.

```c filename=unfold_quantifier.c
void check(int32* data) { data[0] = 0; return; }
```

```click
resource bounded(data: int32*) {
    field value: int32;
    owns data[0..10];
    fact 0 <= value;
}
verifying "unfold_quantifier.c";
void check(int32* data) {
    consumes before: bounded(data);
} by {
    let { value: p } = unfold(before);
    step();
    have forall (k: int32) {
        0 <= k and to_integer(k) < to_integer(p + 1) implies data[k] == data[k]
    } by { intro(); intro(); normalize(); }
    step();
}
```

```expect
fail: not established
```
