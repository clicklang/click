# A statement may update a parenthesized lvalue

A parenthesized lvalue designates the object it encloses (C11 6.5.1p5), so
`(*count)++;` increments `*count` and `(pos) += (n);` adds to `pos`. Statements
that start with `(` were refused with "expected statement, got `(`". Linux
`lib/cmdline.c` writes `(*str)++;`, and cn-cbor's `TAKE` macro expands to
`(pos) += (n);`. A parenthesized memory lvalue now takes the memory-lvalue
statement path, and `( name )` takes the scalar path, including after a prefix
`++` or `--`. The parentheses do not regroup: `(*count)++` updates the counter,
not the pointer.

```c filename=parenthesized_update.c
void tally(int *count, int n)
{
	(*count)++;
	++(*count);
	(*count) += n;
}

int advance(int pos, int n)
{
	(pos) += (n);
	--(pos);
	return pos;
}
```

```click
verifying "parenthesized_update.c";

void tally(int32 *count, int32 n) {
    requires 0 <= count[0] and count[0] < 100;
    requires 0 <= n and n < 100;
    owns count[0..1];
    ensures count[0] == old(count[0]) + 2 + n;
} by {
    execute();
    simp();
}

int32 advance(int32 pos, int32 n) {
    requires 0 <= pos and pos < 100;
    requires 0 <= n and n < 100;
    ensures result == pos + n - 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
