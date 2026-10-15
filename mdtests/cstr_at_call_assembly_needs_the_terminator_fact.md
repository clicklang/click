# Assembling a viewed C string at a call needs every body fact

The negative twin of
[`cstr_at_call_assembles_a_view_from_owned_bytes.md`](cstr_at_call_assembles_a_view_from_owned_bytes.md).
`measure` owns the bytes and states every fact of `cstr_at(src, n)` except
the terminator `src[n] == '\0'`. The bytes alone are not a C string of length
`n`, so the call cannot assemble the view its callee requires and is refused.

```c filename=cstr_at_call_assembly_needs_the_terminator_fact.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
import click::cstr;

verifying "cstr_at_call_assembly_needs_the_terminator_fact.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
}

uint64 measure(uint8* src, uint64 n) {
    owns src[0..n + 1u64];
    requires n < 18446744073709551615u64;
    requires forall (k: uint64) { 0u64 <= k and k < n implies src[k] != '\0' };
    requires forall (k: uint64) { 0u64 <= k and k < n + 1u64 implies defined(src[k]) };
    ensures result == n;
} by {
    execute();
    simp();
}
```

```expect
fail: selected resource `views cstr_at(src, n)`
```
