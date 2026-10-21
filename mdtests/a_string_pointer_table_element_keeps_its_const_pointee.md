# A string-pointer table element keeps its const pointee

The elements of `static const char *const units_10[]` point to `const char`.
Initializing a `char *` from one discards that qualification, which C forbids
without a cast (C11 6.5.16.1p1), so the declaration is refused.

```c filename=discard_table_const.c
char first_letter(int i)
{
	static const char *const units_10[] = {
		"", "k", "M", "G", "T", "P", "E", "Z", "Y",
	};
	char *unit = units_10[i];

	return unit[0];
}
```

```click
verifying "discard_table_const.c";

char first_letter(int32 i) {
    requires i == 1;
    ensures result == 107;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot discard const qualification from a pointer initializer
```
