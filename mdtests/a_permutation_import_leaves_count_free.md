# a permutation import leaves count free

`import click::permutation;` puts the module in scope, not its names, so a
file may declare its own `count` and still reach the library's as
`permutation::count`.

```click
import click::permutation;

function count(x: int32) -> int32 {
    x + 1
}

theorem own_count() {
    ensures count(1) == 2 by {
        unfold(count(1));
        simp();
    }
}

theorem library_count_is_reflexive(p: int32[], x: int32) {
    ensures permutation::count(p, 0, 3, x) == permutation::count(p, 0, 3, x) by {
        simp();
    }
}
```

```expect
pass
```
