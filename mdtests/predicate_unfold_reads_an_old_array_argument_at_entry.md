# A predicate unfold reads an `old` array argument at entry

A predicate's array parameter reads the memory its argument names. In
`same0(p, old(p))`, `b[0]` is `old(p[0])`, not the current `p[0]`: the
unfolded body is `p[0] == old(p[0])`. `keep_first` writes another cell, so
the body holds. Its companion,
`predicate_unfold_with_an_old_array_argument_refuses_a_changed_cell.md`,
writes `p[0]`, and the same claim is refused. Unfolding used to lower every
array argument in the first argument's memory, which made the body
`p[0] == p[0]` and proved the false claim.

```c filename=old_array_argument.c
int32 keep_first(int32 p[3]) { p[1] = 7; return 0; }
int32 keep_first_solved(int32 p[3]) { p[2] = 7; return 0; }
```

```click
verifying "old_array_argument.c";

predicate same0(a: int32[], b: int32[]) { a[0] == b[0] }

int32 keep_first(int32 p[3]) {
    consumes p[0..3];
    ensures kept: same0(p, old(p)) by {
        step();
        step();
        unfold(same0(p, old(p)));
        close();
    }
}

int32 keep_first_solved(int32 p[3]) {
    consumes p[0..3];
    ensures kept: same0(p, old(p)) by { step(); step(); close(); }
}
```

```expect
pass
```
