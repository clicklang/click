# Prove a remainder identity through aliased state reads

The read at `before` and the current read denote the same cell value. Rewriting
`p[0] == at(before, p[0]) % divisor` replaces both occurrences in the next
equality, leaving `old(p[0]) % divisor == old(p[0]) % divisor % 65521u32`.
The divisor equality alone does not discharge that extra remainder. Rewrite
the divisor in the strict bound, then apply the remainder identity again
using the original read and the constant divisor. This reduces the state
pattern from Adler's four-byte B-lane normalization.

```c filename=probe.c
uint32 observe(uint32 *p, uint32 divisor) { return p[0]; }
```

```click
import click::integer;
verifying "probe.c";
uint32 observe(uint32 *p, uint32 divisor) {
 requires p[0] < divisor;
 requires divisor == 65521u32;
 views p[0];
 ensures result == old(p[0]) % 65521u32;
} by {
 mark before;
 step_until(function.exit);
 have p[0] < divisor;
 apply(integer::uint32_less_than_divisor_implies_remainder_is_value(p[0], divisor));
 have p[0] == at(before, p[0]) % divisor by {
  have at(before, p[0]) == p[0] by known();
  rewrite(at(before, p[0]), p[0]);
  known();
 }
 have p[0] < 65521u32 by {
  rewrite(65521u32, divisor);
  known();
 }
 have at(before, p[0]) < 65521u32 by known();
 apply(integer::uint32_less_than_divisor_implies_remainder_is_value(at(before, p[0]), 65521u32));
 have p[0] == at(before, p[0]) % 65521u32 by known();
 solve();
}
```
```expect
pass
```
