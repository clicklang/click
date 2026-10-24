# A branch interface exports a quantified fact over a local array

Both arms prove `forall k < 2 { tmp[k] != 0 }` over the local `char tmp[4]`,
and the join exports it. Each arm checks an interface fact by lowering it as a
`have` of the same text in that arm lowers: `tmp[k]` reads one byte, the
array's element type, and the quantifier is the one a `have` binds. The
interface used to read the local array as `int32` elements and number its
quantifiers apart, so a quantified fact over memory never matched the arm's
proof of it.

```c filename=a_branch_interface_exports_a_quantified_fact_over_a_local_array.c
int b(int j)
{
	char tmp[4];
	tmp[0] = 'a';
	tmp[1] = 'b';
	if (j)
		tmp[0] = 'c';
	tmp[2] = 0;
	return j;
}
```

```click
verifying "a_branch_interface_exports_a_quantified_fact_over_a_local_array.c";
int32 b(int32 j) {
    ensures true;
} by {
    step();
    step();
    step();
    branch ensuring {
        fact forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 };
    } then {
        step();
        have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
    } else {
        have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
    }
    execute();
    simp();
}
```

```expect
pass
```
