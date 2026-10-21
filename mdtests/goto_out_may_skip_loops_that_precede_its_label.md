# `goto out` may skip loops that precede its label

`string_get_size` in Linux `lib/string_helpers.c` jumps over its work when
there is nothing to convert:

```text
if (size == 0)
	goto out;
while (blk_size >> 32) { ... }
...
 out:
	if (i >= ARRAY_SIZE(units_2))
		unit = "UNK";
	else
		unit = units_str[units_base][i];
```

A loop or switch may come before every label of a function. Each such loop
then runs in full or is skipped whole, so no jump enters, leaves, or
re-enters it. A label may also govern an `if` whose arms contain no labels,
jumps, or loops. Below, `execute()` takes the jump when `size == 0`. The
other case needs the loop's invariant, so the proof splits on it first.

```c filename=goto_out.c
int scale(unsigned long size, int i)
{
	int unit;

	if (size == 0)
		goto out;

	while (i < 3)
		i++;

 out:
	if (i >= 9)
		unit = 9;
	else
		unit = i;
	return unit;
}
```

```click
verifying "goto_out.c";

int32 scale(uint64 size, int32 i) {
    requires i == 0;
    ensures (size == 0 and result == 0) or (size != 0 and result == 3);
} by {
    if size == 0 {
        execute();
        simp();
    } else {
        step();
        step();
        step();
        loop {
            decreases 3 - i;
            invariant i >= 0 and i <= 3;
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
