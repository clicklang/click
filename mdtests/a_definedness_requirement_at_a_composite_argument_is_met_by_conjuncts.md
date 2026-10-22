# A definedness requirement at a composite argument is met conjunct by conjunct

`needs_def` requires `defined((t + pos) + 4)`. Applied at `pos := r - x`,
that requirement is the no-overflow conditions of its own two sums. The fact
the caller states, `defined((t + (r - x)) + 4)`, also carries the condition
of `r - x`, nested differently, so it is not the same proposition. A listed
or available fact meets a conjunction when each conjunct is met.

```click
import click::machine_integer;
import click::integer;
theorem lemma_def(t: int32, pos: int32) {
 requires 0 <= t; requires t <= 1000; requires 0 <= pos; requires pos <= 1000;
 ensures defined(t + pos) and defined((t + pos) + 4) by {
  have to_integer(t) + to_integer(pos) >= -2147483648 by arithmetic() using { 0 <= t; 0 <= pos; };
  have to_integer(t) + to_integer(pos) <= 2147483647 by arithmetic() using { to_integer(t) <= 1000; to_integer(pos) <= 1000; };
  apply(int32_add_defined_by_integer_bounds(t, pos));
  apply(int32_add_to_integer(t, pos)) using { defined(t + pos); };
  have to_integer(t + pos) + to_integer(4) >= -2147483648 by arithmetic() using { to_integer(t + pos) == to_integer(t) + to_integer(pos); 0 <= t; 0 <= pos; };
  have to_integer(t + pos) + to_integer(4) <= 2147483647 by arithmetic() using { to_integer(t + pos) == to_integer(t) + to_integer(pos); to_integer(t) <= 1000; to_integer(pos) <= 1000; };
  apply(int32_add_defined_by_integer_bounds(t + pos, 4));
  both { assumption(); } and { assumption(); }
 }
}
theorem needs_def(t: int32, pos: int32) {
 requires defined(t + pos);
 requires defined((t + pos) + 4);
 ensures to_integer((t + pos) + 4) == to_integer(t + pos) + 4 by {
  apply(int32_add_to_integer(t + pos, 4)) using { defined((t + pos) + 4); };
  simp();
 }
}
theorem caller(t: int32, r: int32, x: int32) {
 requires 0 <= t; requires t <= 1000; requires 0 <= x; requires x <= r; requires r <= 1000;
 ensures true by {
  apply(int32_nonnegative_subtract_within_value_is_defined(r, x)) using { 0 <= x; x <= r; };
  have 0 <= to_integer(r - x) by simp();
  have to_integer(r - x) <= 1000 by simp();
  apply(lemma_def(t, r - x));
  have defined(t + (r - x)) by assumption();
  have defined((t + (r - x)) + 4) by assumption();
  apply(needs_def(t, r - x)) using { defined(t + (r - x)); defined((t + (r - x)) + 4); };
  simp();
 }
}
```

```expect
pass
```
