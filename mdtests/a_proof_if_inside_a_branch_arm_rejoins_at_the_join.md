# A proof `if` inside a `branch` arm rejoins at the join

A proof `if` that ends a `branch` arm splits that arm's path in two. Its cases
rejoin where they end, keeping what both establish, and the `branch` join
checks its interface on the rejoined arm; neither case runs to the function
exit. A proof `if` earlier in the arm rejoins before the rest of the arm, as at
the top level.

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
 ensures 0 <= result and result <= 1 by {
 step();
 step();
 branch ensuring {
  fact 0 <= x;
  fact x <= 1;
 } then {
  step();
  if c == 0 {
   have 0 <= x by { auto(); }
   have x <= 1 by { auto(); }
  } else {
   have 0 <= x by { auto(); }
   have x <= 1 by { auto(); }
  }
 } else {
  if c == 0 {
   have 0 <= x by { auto(); }
  } else {
   have 0 <= x by { auto(); }
  }
  have x <= 1 by { auto(); }
 }
 execute();
 simp();
 }
}
```

```expect
pass
```
