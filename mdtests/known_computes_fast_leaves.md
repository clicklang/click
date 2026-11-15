# known computes fast leaves without searching

`known()` combines indexed facts with goal-local arithmetic, identity, and
constructor checks. Pure function calls still need an explicit unfold.

```click
spec enum Choice { Empty, Full(Integer) }
function twice(x: Integer) -> Integer { x + x }

theorem computed_leaves(x: Integer, y: Integer) {
    requires x < y;
    ensures true by known();
    ensures 1 + 1 == 2 by known();
    ensures x + 1 > x by known();
    ensures x + y - y == x by known();
    ensures x * 0 == 0 by known();
    ensures x < y and x + 1 > x by known();
    ensures y < x or x + 1 > x by known();
    ensures not(Choice::Empty == Choice::Full(x)) by known();
    ensures twice(x) == x + x by { unfold(twice(x)); known(); }
}

theorem native_identity(x: uint32, y: uint32) {
    ensures x + y == y + x by known();
    ensures x - x == 0u32 by known();
}
```

```expect
pass
```
