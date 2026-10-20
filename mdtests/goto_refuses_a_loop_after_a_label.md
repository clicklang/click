# `goto` refuses a loop after a label

The forward-`goto` slice accepts loops and switches only before every label
([`goto_out_may_skip_loops_that_precede_its_label.md`](goto_out_may_skip_loops_that_precede_its_label.md)).
A loop after a label would run on both the jumping and the falling-through
path, which that slice does not model, so it is refused by name.

```c filename=loop_after_label.c
int count(int n)
{
	int i = 0;

	if (n < 0)
		goto out;
	i = 1;
 out:
	i = i + 1;
	while (i < 3)
		i++;
	return i;
}
```

```click
verifying "loop_after_label.c";

int32 count(int32 n) {
    ensures result == 3;
} by {
    execute();
    simp();
}
```

```expect
fail: the goto slice supports loops and switches only before every label
```
