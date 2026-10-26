# An interface fact through a pure function holds as its arm proves it

`tmp[tl(j)] == 0u8` reads through a pure function application. In each case,
`tl(j)` equals a constant, so the arm's `have` reads the cell that constant
names and the fact holds outright. The join checks each arm's interface fact
with the same lowering, under the same facts, so it holds there too; it used
to be lowered with condition reasoning deferred and its read left symbolic,
which no fact in the arm matched.

```c filename=an_interface_fact_through_a_pure_function_holds_as_its_arm_proves_it.c
int n(int j)
{
	char tmp[4];
	tmp[0] = 'a';
	tmp[1] = 'b';
	tmp[2] = 0;
	tmp[3] = 0;
	return j;
}
```

```click
verifying "an_interface_fact_through_a_pure_function_holds_as_its_arm_proves_it.c";
function tl(j: int32) -> uint64 {
    if j == 0 { 0u64 } else { (uint64) j + 1u64 }
}
int32 n(int32 j) {
    requires 1 <= j and j <= 2;
    ensures true;
} by {
    step();
    step();
    step();
    step();
    step();
    if j == 1 ensuring {
        fact tmp[tl(j)] == 0u8;
    } then {
        have tl(j) == 2u64 by { unfold(tl(j)); solve(); }
        have tmp[tl(j)] == 0u8 by { normalize(); }
    } else {
        have j == 2 by { solve() using { 1 <= j; j <= 2; j != 1; }; }
        have tl(j) == 3u64 by { unfold(tl(j)); solve(); }
        have tmp[tl(j)] == 0u8 by { normalize(); }
    }
}
```

```expect
pass
```
