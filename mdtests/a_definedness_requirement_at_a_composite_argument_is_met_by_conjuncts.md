# A definedness requirement at a composite argument is met conjunct by conjunct

`needs_def` requires `defined((t + pos) + 4)`. Applied at `pos := r - x`,
that requirement is the no-overflow conditions of its own two sums. The fact
the caller states, `defined((t + (r - x)) + 4)`, also carries the condition
of `r - x`, nested differently, so it is not the same proposition. A listed
or available fact meets a conjunction when each conjunct is met.

```click
import click::integer;
theorem lemma_def(t: int32, pos: int32) {
 requires 0 <= t; requires t <= 1000; requires 0 <= pos; requires pos <= 1000;
 ensures defined(t + pos) and defined((t + pos) + 4) by {
  have to_integer(t) + to_integer(pos) >= -2147483648 by solve() using { 0 <= t; 0 <= pos; };
  have to_integer(t) + to_integer(pos) <= 2147483647 by solve() using { to_integer(t) <= 1000; to_integer(pos) <= 1000; };
  have defined(t + pos);
  have to_integer(t + pos) == to_integer(t) + to_integer(pos);
  have to_integer(t + pos) + to_integer(4) >= -2147483648 by solve() using { to_integer(t + pos) == to_integer(t) + to_integer(pos); 0 <= t; 0 <= pos; };
  have to_integer(t + pos) + to_integer(4) <= 2147483647 by solve() using { to_integer(t + pos) == to_integer(t) + to_integer(pos); to_integer(t) <= 1000; to_integer(pos) <= 1000; };
  have defined((t + pos) + 4);
  both { assumption(); } and { assumption(); }
 }
}
theorem needs_def(t: int32, pos: int32) {
 requires defined(t + pos);
 requires defined((t + pos) + 4);
 ensures to_integer((t + pos) + 4) == to_integer(t + pos) + 4 by {
  have to_integer((t + pos) + 4) == to_integer((t + pos)) + to_integer(4);
  solve();
 }
}
theorem caller(t: int32, r: int32, x: int32) {
 requires 0 <= t; requires t <= 1000; requires 0 <= x; requires x <= r; requires r <= 1000;
 ensures true by {
  have defined(r - x);
  have 0 <= to_integer(r - x) by solve();
  have to_integer(r - x) <= 1000 by solve();
  apply(lemma_def(t, r - x));
  have defined(t + (r - x)) by assumption();
  have defined((t + (r - x)) + 4) by assumption();
  apply(needs_def(t, r - x)) using { defined(t + (r - x)); defined((t + (r - x)) + 4); };
  solve();
 }
}
```

```expect
pass
```
