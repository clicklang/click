# a `uint64` branch's negation refutes the other arm's hypothesis

On the path where `x >= 32u64`, the hypothesis `x < 32u64` of the first
claim is that comparison's arithmetic negation, and on the other path
`32u64 <= x` negates `x < 32u64`. `contradiction` recognizes the pair in
every order family, as it does for `int32`, so `auto` closes both claims of
`fit` exactly as it closes `fit32`'s. `fit_explicit` writes the refuting
step itself.

```c filename=fit.c
uint64 fit(uint64 x)
{
	if (x >= 32)
		return 31;
	return x;
}

int32 fit32(int32 x)
{
	if (x >= 32)
		return 31;
	return x;
}

uint64 fit_explicit(uint64 x)
{
	if (x >= 32)
		return 31;
	return x;
}
```

```click
verifying "fit.c";

uint64 fit(uint64 x) {
    ensures x < 32u64 implies result == x;
    ensures 32u64 <= x implies result == 31u64;
} by auto();

int32 fit32(int32 x) {
    ensures x < 32 implies result == x;
    ensures 32 <= x implies result == 31;
} by auto();

uint64 fit_explicit(uint64 x) {
    requires x >= 32u64;
    ensures x < 32u64 implies result == x;
} by {
    execute();
    have x < 32u64 implies result == x by {
        intro();
        contradiction(x < 32u64);
    }
    assumption();
}
```

```expect
pass
```
