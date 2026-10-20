# A string literal is distinct from a local array

A string literal is an object of its own (C11 6.4.5p6). Only another literal
with the same bytes may share its storage, so a store to a local array never
changes a literal. `string_get_size` in Linux `lib/string_helpers.c` writes
`tmp[0] = '\0'` and later reads a unit name such as `"UNK"`. Click used to
treat every literal as a possible alias of every declared object: a load from
the literal then met the array's cell and was refused.

```c filename=literal_and_array.c
int literal_after_int_store(void)
{
	int tmp[1];
	const char *unit;

	tmp[0] = 0;
	unit = "a";
	return unit[0];
}

int literal_after_char_store(int i)
{
	char tmp[12];
	const char *unit;

	tmp[0] = '\0';
	if (i >= 9)
		unit = "UNK";
	else
		unit = "";
	return unit[0] + tmp[0];
}
```

```click
verifying "literal_and_array.c";

int32 literal_after_int_store() {
    ensures result == 97;
} by {
    execute();
    simp();
}

int32 literal_after_char_store(int32 i) {
    requires i == 9;
    ensures result == 85;
} by {
    execute();
    simp();
}
```

```expect
pass
```
