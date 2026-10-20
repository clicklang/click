# `string_get_size` unit tables are static string-pointer tables

`string_get_size` in Linux `lib/string_helpers.c` names its units through
three function-scope `static` tables, unchanged here:

- `units_10` and `units_2` are arrays of `const char *const` whose elements
  are string literals. A string literal is an array with static storage
  duration, and in an initializer it converts to a pointer to its first
  element (C11 6.3.2.1p3, 6.4.5p6).
- `units_str` is an array of `const char *const *const`, a pointer to the
  first element of each table. It is designated by enumeration constants.
- `unit = units_str[units_base][i]` indexes the table of tables, then the
  table, as `ARRAY_SIZE(units_2)` guards.

`unit_letter` reads the binary table and `unit_initial`, whose `units` has
only `STRING_UNITS_NO_SPACE` set, the decimal one.

Const qualification below the immediate pointee, as in `const char *const *`,
changes no behavior and is accepted. The pointer each cell holds keeps its own
qualification, so `unit[0]` reads a literal through a `const char *`.

```c filename=unit_tables.c
#define BIT(nr) (1UL << (nr))
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

enum string_size_units {
	STRING_UNITS_10,	/* use powers of 10^3 (standard SI) */
	STRING_UNITS_2,		/* use binary powers of 2^10 */
	STRING_UNITS_MASK	= BIT(0),

	/* Modifiers */
	STRING_UNITS_NO_SPACE	= BIT(30),
	STRING_UNITS_NO_BYTES	= BIT(31),
};

char unit_letter(const enum string_size_units units, int i, int k)
{
	enum string_size_units units_base = units & STRING_UNITS_MASK;
	static const char *const units_10[] = {
		"", "k", "M", "G", "T", "P", "E", "Z", "Y",
	};
	static const char *const units_2[] = {
		"", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi", "Yi",
	};
	static const char *const *const units_str[] = {
		[STRING_UNITS_10] = units_10,
		[STRING_UNITS_2] = units_2,
	};
	const char *unit;

	if (i >= ARRAY_SIZE(units_2))
		unit = "UNK";
	else
		unit = units_str[units_base][i];
	return unit[k];
}

char unit_initial(const enum string_size_units units, int i)
{
	enum string_size_units units_base = units & STRING_UNITS_MASK;
	static const char *const units_10[] = {
		"", "k", "M", "G", "T", "P", "E", "Z", "Y",
	};
	static const char *const units_2[] = {
		"", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei", "Zi", "Yi",
	};
	static const char *const *const units_str[] = {
		[STRING_UNITS_10] = units_10,
		[STRING_UNITS_2] = units_2,
	};
	const char *unit;

	if (i >= ARRAY_SIZE(units_2))
		unit = "UNK";
	else
		unit = units_str[units_base][i];
	return unit[0];
}
```

```click
verifying "unit_tables.c";

char unit_letter(uint32 units, int32 i, int32 k) {
    requires units == 1 and i == 1 and k == 1;
    ensures result == 105;
} by {
    execute();
    simp();
}

char unit_initial(uint32 units, int32 i) {
    requires units == 1073741824u32 and i == 2;
    ensures result == 77;
} by {
    execute();
    simp();
}
```

```expect
pass
```
