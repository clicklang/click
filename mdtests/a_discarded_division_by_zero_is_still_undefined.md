# A discarded division by zero is still undefined

An expression statement evaluates its expression even though it discards the
value (C11 6.8.3p2). `(void)(1 / x);` divides by zero when `x == 0`, so it is
refused rather than dropped.

```c filename=discarded_division.c
int discard(int x)
{
	(void)(1 / x);
	return 0;
}
```

```click
verifying "discarded_division.c";

int32 discard(int32 x) {
    requires x == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior
```
