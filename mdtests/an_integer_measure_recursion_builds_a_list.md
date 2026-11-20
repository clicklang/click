# An integer-measure recursion builds a list

A recursive pure function whose measure is an `int32` may take parameters of
other types and return any type: `repeat_value` counts `n` down while it
builds a `List<uint64>`, carrying a `uint64` value along.

```click
function repeat_value(n: int32, value: uint64) -> List<uint64>
    decreases n
{
    if n <= 0 {
        List<uint64>::Nil
    } else {
        List<uint64>::Cons(value, repeat_value(n - 1, value))
    }
}

theorem two_copies(value: uint64) {
    ensures repeat_value(2, value)
        == List::Cons(value, List::Cons(value, List::Nil)) by {
        unfold(repeat_value(0, value));
        unfold(repeat_value(1, value));
        unfold(repeat_value(2, value));
        solve();
    }
}
```

```expect
pass
```
