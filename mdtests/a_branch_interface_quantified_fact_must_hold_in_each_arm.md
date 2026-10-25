# A branch interface quantified fact must hold in each arm

The then arm does not prove the quantified interface fact, so the join refuses
it.

```c filename=a_branch_interface_quantified_fact_must_hold_in_each_arm.c
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
verifying "a_branch_interface_quantified_fact_must_hold_in_each_arm.c";
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
    } else {
        have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
    }
}
```

```expect
fail: `branch ensuring` did not establish fact
```
