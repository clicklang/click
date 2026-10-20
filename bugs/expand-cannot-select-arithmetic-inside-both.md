# Expansion cannot select arithmetic inside `both`

Soundness: not soundness. The theorem verifies, and whole-claim expansion
produces independently verifiable source. Selecting the existing arithmetic
tactic by its source location fails before expansion. No false acceptance is
known.

Save this as `/tmp/both-source.click`, preserving the line breaks:

```click
theorem pair(a: Integer, b: Integer) {
 requires 0 <= a;
 requires 0 <= b;
 ensures 0 <= a and 0 <= b by {
  both {
   arithmetic() using { 0 <= a; };
  } and {
   arithmetic() using { 0 <= b; };
  }
 }
}
```

`click verify /tmp/both-source.click` succeeds. The first arithmetic tactic
starts at line 6, column 4, but:

```console
click expand /tmp/both-source.click:6:4
```

fails with `no smart tactic's source contains this location`. In contrast,
`click expand --claim pair.ensures_0 /tmp/both-source.click` succeeds, and its
output verifies independently. This was reproduced while repairing Integer
goal rendering; the source-selection defect also occurs in the smaller
example above, which needs no rewrite or machine arithmetic.

The source-selection invariant should include smart tactics inside both arms
of a supported `both` proof. Add a regression that selects the arithmetic
tactic at each arm's actual line and column, expands the correct owning claim,
and verifies the emitted source. Keep whole-claim expansion working, and
check that an unrelated source location remains rejected.
