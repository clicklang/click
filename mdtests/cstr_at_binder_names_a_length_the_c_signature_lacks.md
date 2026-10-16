# A binder names the length of a C string its signature does not carry

`string_length` takes only the pointer. Its contract binds the string it
views, `views str: cstr_at(s, _);`, and names the string's length as
`str.len` in its postcondition. The `_` is a value parameter of the
contract: the callee is specified for every length, and each call takes the
length from the string its caller holds. `measure` holds
`views cstr_at(src, n)`, so the call to `string_length(src)` takes `n` and
returns it, without the length passing through C.

```c filename=cstr_at_binder_names_a_length_the_c_signature_lacks.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::cstr;

verifying "cstr_at_binder_names_a_length_the_c_signature_lacks.c";

extern uint64 string_length(const uint8* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    ensures result == n;
} by {
    execute();
    simp();
}
```

```expect
pass
```
