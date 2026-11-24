# `defined` claims its root operation's domain, with its operands as values

`defined(a + b + c)` is `defined((a + b) + c)`: it claims that adding `c` to
the value of `a + b` is defined. The inner addition is an operand, and its
domain is owed wherever the expression is written, as any term's is. Both
domains together are the conjunction `defined(a + b) and defined(a + b + c)`,
whose right side is read only where its left side holds.

```click
theorem both(a: int32, b: int32, c: int32) {
    requires defined(a + b) and defined(a + b + c);
    ensures to_integer(a + b) + to_integer(c) <= 2147483647 by { close(); }
    ensures to_integer(a) + to_integer(b) <= 2147483647 by { close(); }
}

theorem guarded(a: int32, b: int32, c: int32, x: int32) {
    requires defined(a + b) and defined(a + b + c) implies x == 1;
    ensures 1 == 1 by close();
}
```

```expect
pass
```
