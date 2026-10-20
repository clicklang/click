# `string_get_size` tables take designators, `sizeof`, and literal branches

Three C forms from `string_get_size` in Linux `lib/string_helpers.c`, unchanged:

- An inferred-length array may be initialized through designators, here
  enumeration constants (C11 6.7.9p6). Its length is one past the largest
  initialized index, and any element no initializer names is zero.
- `sizeof` of a complete array object is the whole array's size, not a
  pointer's (C11 6.5.3.4p2).
- The branches of `c ? "" : " "` are arrays of different lengths, and each
  converts to a pointer to its first element, so the conditional has type
  `char *` (C11 6.3.2.1p3).

```c filename=size_tables.c
enum string_size_units {
	STRING_UNITS_10,
	STRING_UNITS_2,
};

unsigned int divisor_of(int units_base)
{
	static const unsigned int divisor[] = {
		[STRING_UNITS_10] = 1000,
		[STRING_UNITS_2] = 1024,
	};

	return divisor[units_base];
}

unsigned int padded(int index)
{
	static const unsigned int table[] = { [3] = 7 };

	return table[index];
}

unsigned long tmp_size(void)
{
	char tmp[12];

	return sizeof(tmp);
}

char separator(int no_space)
{
	const char *space = no_space ? "" : " ";

	return space[0];
}
```

```click
verifying "size_tables.c";

uint32 divisor_of(int32 units_base) {
    requires units_base == 1;
    ensures result == 1024;
} by {
    execute();
    simp();
}

uint32 padded(int32 index) {
    requires index == 2;
    ensures result == 0;
} by {
    execute();
    simp();
}

uint64 tmp_size() {
    ensures result == 12;
} by {
    execute();
    simp();
}

char separator(int32 no_space) {
    ensures (no_space != 0 and result == 0) or (no_space == 0 and result == 32);
} by {
    execute();
    simp();
}
```

```expect
pass
```
