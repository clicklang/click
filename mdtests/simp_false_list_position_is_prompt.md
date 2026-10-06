# A false list position fails promptly

The available adjacency fact has different arguments from the goal.

```click
function adjacent(xs: List<int32>, first: int32, second: int32) -> int32
    decreases xs
{
    match xs {
        List::Nil => 0,
        List::Cons(head, tail) =>
            if head == first {
                match tail {
                    List::Nil => 0,
                    List::Cons(next, rest) => if next == second { 1 } else { 0 },
                }
            } else {
                adjacent(tail, first, second)
            },
    }
}

theorem wrong_position(xs: List<int32>, tail: List<int32>, first: int32, second: int32, flag: int32) {
    requires xs == List<int32>::Cons(first, tail);
    requires adjacent(xs, first, second) == 1;
    ensures flag != 0 implies adjacent(xs, second, first) == 1 by {
        simp();
    }
}
```

```expect
fail: could not establish `flag != 0 implies adjacent(xs, second, first) == 1`
```
