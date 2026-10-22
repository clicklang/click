# A failed auto reports the proposition written in the have

This uint64 difference sends search through definedness and Integer bridges.
The bound does not follow from the contract. Its diagnostic must name auto
and the stated bound, rather than an internal normalization goal.

```c filename=bound.c
unsigned long bound(unsigned long a, unsigned long b) { return a; }
```

```click
verifying "bound.c";
uint64 bound(uint64 a, uint64 b) { ensures result == a; } by {
    have to_integer(a) <= to_integer(b - b % 4u64) by auto();
    execute(); simp();
}
```

```expect
fail: `auto` could not prove `to_integer(a) <= to_integer((b - (b % 4u64)))`
```
