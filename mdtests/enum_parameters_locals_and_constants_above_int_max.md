# Enum parameters, locals, and constants above `INT_MAX`

Linux `include/linux/string_helpers.h` declares `STRING_UNITS_NO_BYTES =
BIT(31)`, a value `int` does not hold, and `string_get_size` in
`lib/string_helpers.c` takes a `const enum string_size_units` parameter and
declares a local of that type. GCC accepts an enumerator above `INT_MAX` when
no value is negative: the enumeration's compatible type is `unsigned int`, and
because one constant does not fit `int`, every constant has the enumerated type
(C23 6.7.2.2p15; GCC 13 types them so, while Clang 18 keeps the fitting ones
`int`). Enum parameters, locals, and returns take the compatible type, so the
sidecar spells them `uint32`. The enumeration and the first statement of
`string_get_size` are unchanged.

```c filename=string_units.c
#define BIT(nr) (1UL << (nr))

enum string_size_units {
	STRING_UNITS_10,	/* use powers of 10^3 (standard SI) */
	STRING_UNITS_2,		/* use binary powers of 2^10 */
	STRING_UNITS_MASK	= BIT(0),

	/* Modifiers */
	STRING_UNITS_NO_SPACE	= BIT(30),
	STRING_UNITS_NO_BYTES	= BIT(31),
};

int binary_units(const enum string_size_units units)
{
	enum string_size_units units_base = units & STRING_UNITS_MASK;

	return units_base == STRING_UNITS_2;
}

unsigned int no_bytes_flag(void)
{
	return STRING_UNITS_NO_BYTES;
}

enum string_size_units base_of(enum string_size_units units)
{
	return units & STRING_UNITS_MASK;
}
```

```click
verifying "string_units.c";

int32 binary_units(uint32 units) {
    requires units == 2147483649u32;
    ensures result == 1 by auto();
}

uint32 no_bytes_flag() {
    ensures result == 2147483648u32 by auto();
}

uint32 base_of(uint32 units) {
    requires units == 1073741824u32;
    ensures result == 0 by auto();
}
```

```expect
pass
```
