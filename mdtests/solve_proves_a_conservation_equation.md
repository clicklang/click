# The implicit closer proves a machine conservation equation

`capacity - amount == used + (available - amount)` over `int32` is proved
through its `Integer` reading: the equality fact `capacity == used +
available` is carried to `Integer`, each operation is shown defined and
observed term by term, and both bounds of the `Integer` equality are refuted.
A machine equality is the equality of its `to_integer` observations, so that
closes the goal. The conjunction goal
is split and each side proved the same way. The shrink claim states definedness
explicitly: its word equality alone also holds modulo 2^32 when an intermediate
subtraction underflows, so it cannot stand in for an overflow check.

```click
theorem shrink_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity - amount);
    ensures defined(available - amount) and defined(used + (available - amount)) and
        capacity - amount == used + (available - amount);
}

theorem grow_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(available + amount) and defined(used + (available + amount)) and
        capacity + amount == used + (available + amount) by {
        have to_integer(capacity) + to_integer(amount) <= 2147483647 by known();
        have to_integer(available) + to_integer(amount) <= 2147483647 by {
            solve() using { 0 <= used; capacity == used + available; to_integer(capacity) + to_integer(amount) <= 2147483647; };
        }
        have -2147483648 <= to_integer(available) + to_integer(amount) by {
            solve() using { 0 <= available; 0 <= amount; };
        }
        have defined(available + amount) by known();
        have defined(used + (available + amount)) by solve();
        have capacity + amount == used + (available + amount) by solve();
        known();
    }
}
```

```expect
pass
```
