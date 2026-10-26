# A proof `if` inside a `branch` arm keeps only what both cases establish

The cases of a proof `if` that ends a `branch` arm rejoin where they end,
keeping what both establish, and the `branch` join checks its interface on
that rejoined arm. Here only the `c == 0` case proves `x == 0 or c == 0`; the
other has `x == 1`. The fact does not survive the rejoin, so the join refuses
it.

```c filename=branch.c
int32 pick(int32 a, int32 c) {
 int32 x = 0;
 if (a) x = 1;
 return x;
}
```
```click
verifying "branch.c";
int32 pick(int32 a, int32 c) {
 ensures result == 0 or c == 0 or result == 1 by {
 step();
 step();
 branch ensuring {
  fact x == 0 or c == 0;
 } then {
  step();
  if c == 0 {
   have x == 0 or c == 0;
  } else {
   have 0 <= x;
  }
 } else {
  have x == 0 or c == 0;
 }
 }
}
```

```expect
fail: `branch ensuring` did not establish fact `x == 0 or c == 0`
```
