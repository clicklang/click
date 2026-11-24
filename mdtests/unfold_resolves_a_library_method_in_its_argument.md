# Unfold resolves a library method in its argument

A function argument can use methods of a Click library type, such as
`v.len()` for a `Vec`. The receiver's type resolves that method before
ordinary `unfold` lowers the defining equation and checks the range guards.

```click
import click::rust::vec;

function total(hi: uint64) -> Integer {
    (0..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem empty(v: Vec<uint32>) {
    requires v.len() == 0u64;
    ensures total(v.len()) == 0 by {
        have to_integer(v.len()) <= to_integer(0u64);
        unfold(total(v.len()));
        close();
    }
}
```

```expect
pass
```
