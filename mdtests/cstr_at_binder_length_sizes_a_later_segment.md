# A binder's length sizes a later memory clause

`copy_string`'s contract binds the source string and then owns
`dst[0..str.len + 1u64]`: the clause after the binder names the length the
binder's `_` introduces, so the destination's size follows the string the
caller passes. `use` holds `cstr_at(src, n)` and owns `n + 1` destination
bytes, which is exactly what the call takes.

```c filename=cstr_at_binder_length_sizes_a_later_segment.c
void copy_string(uint8 *dst, const uint8 *src);

void use(uint8 *dst, const uint8 *src, uint64 n)
{
	copy_string(dst, src);
}
```

```click
import click::cstr;

verifying "cstr_at_binder_length_sizes_a_later_segment.c";

extern void copy_string(uint8* dst, const uint8* src) {
    views str: cstr_at(src, _);
    owns dst[0..str.len + 1u64];
}

void use(uint8* dst, const uint8* src, uint64 n) {
    views cstr_at(src, n);
    owns dst[0..n + 1u64];
} by {
    execute();
}
```

```expect
pass
```
