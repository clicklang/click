# A parenthesized update of a stored pointer is refused at execution

Linux `lib/cmdline.c` advances a caller's cursor with `(*str)++;`, where `str`
is a `char **`. The statement parses as an update of the stored pointer `*str`,
not of `str`. Execution still refuses a compound update of a pointer held in
memory, however it is spelled (`*str += 1;`, `++*str;`), and names it as a type
mismatch; see `a_statement_may_update_a_parenthesized_lvalue.md` for the integer
cells it updates.

```c filename=cursor_advance.c
void advance(char **str)
{
	(*str)++;
}
```

```click
verifying "cursor_advance.c";

void advance(char **str) {
    owns str[0..1];
    ensures true;
} by {
    execute();
    simp();
}
```

```expect
fail: type mismatch
```
