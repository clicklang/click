# A call map names the string a call assembles from owned bytes

`measure` owns the bytes of a C string of length `n` and states its facts,
but holds no `cstr_at` instance, so nothing held gives `string_length`'s
`str.len` a value. The call map names the instance as a resource term,
`{ str: cstr_at(src, n) }`: the binder takes `n`, and the call assembles the
view from the owned bytes, as
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](cstr_at_call_assembles_a_view_from_owned_bytes.md)
does when the length is a C argument. `relay` names its own binder instead,
`{ str: s }`, which passes on the string it was given.

```c filename=cstr_at_call_map_names_the_string_a_call_assembles.c
uint64 string_length(const uint8 *s);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src);
}

uint64 relay(const uint8 *src)
{
	return string_length(src);
}
```

```click
import click::cstr;

verifying "cstr_at_call_map_names_the_string_a_call_assembles.c";

extern uint64 string_length(const uint8* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 measure(uint8* src, uint64 n) {
    owns src[0..n + 1u64];
    requires n < 18446744073709551615u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies src[k] != '\0' };
    requires src[n] == '\0';
    requires forall (k: uint64) { 0u64 <= k and k < n + 1u64 implies defined(src[k]) };
    ensures result == n;
} by {
    step(string_length(src), { str: cstr_at(src, n) });
    execute();
    simp();
}

uint64 relay(const uint8* src) {
    views s: cstr_at(src, _);
    ensures result == s.len;
} by {
    step(string_length(src), { str: s });
    execute();
    simp();
}
```

```expect
pass
```
