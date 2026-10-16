# A binder does not choose between two held strings

`measure` views the same bytes as two strings, `cstr_at(src, n)` and
`cstr_at(src, m)`. Their facts make `n` and `m` equal, but the call does not
search for that: two held instances agree with the clause's pointer, so the
call cannot choose `str.len` and is refused. A call map such as
`{ str: cstr_at(src, n) }` names the one to use.

```c filename=cstr_at_binder_refuses_an_ambiguous_choice.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n, uint64 m)
{
	return string_length(src);
}
```

```click
import click::cstr;

verifying "cstr_at_binder_refuses_an_ambiguous_choice.c";

extern uint64 string_length(const uint8* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 measure(const uint8* src, uint64 n, uint64 m) {
    views cstr_at(src, n);
    views cstr_at(src, m);
    ensures result == n;
} by {
    execute();
    simp();
}
```

```expect
fail: cannot choose `str.len`
```
