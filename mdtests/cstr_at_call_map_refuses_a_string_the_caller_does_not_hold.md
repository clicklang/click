# A call map cannot name a string the caller does not hold

`measure` holds `cstr_at(src, n)` and names `cstr_at(src, n + 1)` in its call
map. The binder takes `n + 1` from the term, but a call map grants nothing:
the call still requires `views cstr_at(src, n + 1)`, which the caller
neither holds nor can assemble, so it is refused.

```c filename=cstr_at_call_map_refuses_a_string_the_caller_does_not_hold.c
uint64 string_length(const uint8 *s);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src);
}
```

```click
import click::cstr;

verifying "cstr_at_call_map_refuses_a_string_the_caller_does_not_hold.c";

extern uint64 string_length(const uint8* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 measure(const uint8* src, uint64 n) {
    views cstr_at(src, n);
    requires n < 1000u64;
    ensures result == n + 1u64;
} by {
    step(string_length(src), { str: cstr_at(src, n + 1u64) });
    execute();
    simp();
}
```

```expect
fail: views cstr_at(src, n + 1u64)
```
