# An if interface exports a quantified fact with an Integer bound

Each case of a proof `if` proves the fact for its own `j` by instantiating a
constant-bounded one, and the join exports `forall k < j as uint64 + 1u64`,
whose bound is Integer arithmetic in a proof.

```c filename=an_if_interface_exports_a_quantified_fact_with_an_integer_bound.c
int q(int j)
{
	char tmp[4];
	tmp[0] = 'a';
	tmp[1] = 'b';
	tmp[2] = 0;
	return j;
}
```

```click
verifying "an_if_interface_exports_a_quantified_fact_with_an_integer_bound.c";
int32 q(int32 j) {
    requires 0 <= j and j <= 1;
    ensures true;
} by {
    step();
    step();
    step();
    step();
    if j == 0 ensuring {
        fact forall (k: uint64) { 0u64 <= k and k < j as uint64 + 1u64 implies tmp[k] != 0u8 };
    } then {
        have forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 } by { enumerate(); }
        have forall (k: uint64) { 0u64 <= k and k < j as uint64 + 1u64 implies tmp[k] != 0u8 } by {
            intro();
            intro();
            have k < 1u64 by { solve(); }
            instantiate(forall (k: uint64) { 0u64 <= k and k < 1u64 implies tmp[k] != 0u8 }, k);
            assumption();
        }
    } else {
        have 1 <= j by { solve() using { 0 <= j; j != 0; }; }
        have j == 1 by { solve() using { 1 <= j; j <= 1; }; }
        have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
        have forall (k: uint64) { 0u64 <= k and k < j as uint64 + 1u64 implies tmp[k] != 0u8 } by {
            intro();
            intro();
            have k < 2u64 by { solve(); }
            instantiate(forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 }, k);
            assumption();
        }
    }
}
```

```expect
pass
```
