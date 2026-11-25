# An unfolded scalar retains its definedness under a quantifier

After a store, the old resource field retains an evaluation obligation even
though its bounds and explicit definedness are known in the current scope.
The unrelated universal binder must not prevent discharging that obligation.

```c filename=unfold_quantifier.c
void check(int32* data) { data[0] = 0; return; }
```

```click
import click::integer;
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
    have 10 <= 2147483647 by { close(); }
    have p < 2147483647 by {
        apply(integer::int32_less_than_less_equal_transitive(p, 10, 2147483647));
    }
    have defined(p + 1) by {
        apply(integer::int32_increment_below_max_is_defined(p));
    }
    have forall (k: int32) {
        0 <= k and to_integer(k) < to_integer(p + 1) implies data[k] == data[k]
    } by { intro() { intro() { close(); } } }
    step();
}
```

```expect
pass
```
