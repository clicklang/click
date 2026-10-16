# A binder needs a string to take its length from

`measure` views the bytes of `src` but holds no `cstr_at` instance and
writes no call map, so nothing gives `string_length`'s `str.len` a value
and the call is refused with the parameter named.
[`cstr_at_call_map_names_the_string_a_call_assembles.md`](cstr_at_call_map_names_the_string_a_call_assembles.md)
names the instance in a call map instead.

```c filename=cstr_at_binder_needs_a_held_string.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::cstr;

verifying "cstr_at_binder_needs_a_held_string.c";

extern uint64 string_length(const uint8* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 measure(const uint8* src, uint64 n) {
    views src[0..n + 1u64];
    ensures result == n;
} by {
    execute();
    simp();
}
```

```expect
fail: needs a held `cstr_at` instance to give `str.len` its value
```
