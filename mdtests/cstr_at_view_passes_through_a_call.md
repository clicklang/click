# A borrowed C string passes through a call

`views cstr_at(src, n)` borrows the `n + 1` bytes of `src` through its
terminator. `measure` receives that loan and lends the same composite to
`string_length` without opening it: the call needs no unfold, refold, or
restatement of the string's facts. `string_length` stands for a library
function whose contract takes the borrowed string; its length is a C argument
here only because a contract cannot yet name a length its C signature does
not carry.

```c filename=cstr_at_view_passes_through_a_call.c
uint64 string_length(const uint8 *s, uint64 n);

uint64 measure(const uint8 *src, uint64 n)
{
	return string_length(src, n);
}
```

```click
// The resource proposed for `library/cstr.click`, declared here because a
// library module cannot yet export a composite resource: a view of the bytes
// of `p` through its first terminator, with the facts that make them the C
// string of length `len`.
resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}

verifying "cstr_at_view_passes_through_a_call.c";

extern uint64 string_length(const uint8* s, uint64 n) {
    views cstr_at(s, n);
    ensures result == n;
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
