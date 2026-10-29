# An interface fact through a pure function holds as its arm proves it

`tmp[tl(j)] == 0u8` reads through a pure function application. Each arm
proves which constant `tl(j)` equals, then rewrites that equality to check
the stored cell. The interface fact retains its symbolic read when lowered
both in the arm and at the join; equality reasoning belongs in the proof.

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
    if j == 0 { 0u64 } else { j as uint64 + 1u64 }
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
        have tmp[tl(j)] == 0u8 by { rewrite(tl(j) == 2u64); normalize(); }
    } else {
        have j == 2 by { solve() using { 1 <= j; j <= 2; j != 1; }; }
        have tl(j) == 3u64 by { unfold(tl(j)); solve(); }
        have tmp[tl(j)] == 0u8 by { rewrite(tl(j) == 3u64); normalize(); }
    }
}
```

```expect
pass
```
