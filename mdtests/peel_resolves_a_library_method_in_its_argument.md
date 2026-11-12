# Peel resolves a library method in its argument

`peel` opens one layer of a call, as `unfold` does. Its argument may read a
value of a Click library type with that type's methods: here `v.len()`, the
length of a `Vec`. The method is resolved by the receiver's type before the
defining equation is lowered, in the argument and in the `using` premises
alike.

`peel` used to pass its argument through unresolved, so lowering met the
method call itself and refused with "the method `len` was not resolved by its
receiver's type".

```click
import click::rust::vec;

function total(hi: uint64) -> Integer {
    (0..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem empty(v: Vec<uint32>) {
    requires v.len() == 0u64;
    ensures total(v.len()) == 0 by {
        have to_integer(v.len()) <= to_integer(0u64);
        peel(total(v.len())) using { to_integer(v.len()) <= to_integer(0u64); };
        solve();
    }
}
```

```expect
pass
```
