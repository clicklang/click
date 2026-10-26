# A symbolic birth and a unit birth retain an arbitrary entry total

After `n` births and one more, the count is the `int32` sum
`old(count(tok(o))) + (n + 1)`. The postcondition compares it with the exact
Integer total, so the proof first shows that sum is defined: its Integer
bounds follow from the entry count's own definedness requirements, and
`integer::int32_add_defined_by_integer_bounds` turns them into `defined(...)`.

```c filename=population_symbolic_increment_bounded.c
void mint_n(int32* o, int32 n) {}
void increment(int32* o, int32 n) { mint_n(o, n); mint_n(o, 1); }
```

```click
import click::integer;
authorized resource tok(o: int32*) {}
verifying "population_symbolic_increment_bounded.c";
void mint_n(int32* o, int32 n) {
    owns authority(tok(o));
    requires 0 < n;
    requires defined(count(tok(o)) + n);
    produces n of tok(o);
    ensures count(tok(o)) == old(count(tok(o))) + n;
} by { fold(n of tok(o)); }
void increment(int32* o, int32 n) {
    owns authority(tok(o));
    requires defined(count(tok(o)) + n);
    requires defined((count(tok(o)) + n) + 1);
    requires defined(n + 1);
    requires 0 < n;
    requires n < 2147483647;
    ensures count(tok(o)) == old(count(tok(o))) + (n + 1);
} by {
    step_until(function.exit);
    have to_integer(n + 1) == to_integer(n) + 1 by auto();
    have to_integer(old(count(tok(o)))) + to_integer(n + 1) <= 2147483647 by auto();
    have to_integer(old(count(tok(o)))) + to_integer(n + 1) >= -2147483648 by auto();
    have defined(old(count(tok(o))) + (n + 1)) by auto();
    auto();
}
```

```expect
pass
```
