# Integer certificates retain proof-local algebraic bindings

```click
spec enum Count { Value(int32) }
function count_value(count: Count) -> int32 {
    match count { Count::Value(value) => value, }
}
theorem local_count_arithmetic() {
    ensures forall (count: Count) {
        to_integer(count_value(count)) == 3 implies
        to_integer(count_value(count)) + 1 == 4
    } by {
        intro(); intro();
        arithmetic() using { to_integer(count_value(count)) == 3; }
    }
}
```
```expect
pass
```
