# A function with a binder is proved for every length

The binder's `_` is a value parameter of `known_length`'s own contract, so
its body is proved at an arbitrary `t.len`: the requirement `n == t.len`
and the postcondition both name it, and the proof never fixes it. The
caller takes the length from the string it holds. The owning form is
[`cstr_at_owning_binder_keeps_its_length.md`](cstr_at_owning_binder_keeps_its_length.md).

```c filename=cstr_at_binder_length_is_proved_for_every_length.c
uint64 known_length(const uint8 *s, uint64 n)
{
	return n;
}

uint64 measure(const uint8 *src, uint64 m)
{
	return known_length(src, m);
}
```

```click
import click::cstr;

verifying "cstr_at_binder_length_is_proved_for_every_length.c";

uint64 known_length(const uint8* s, uint64 n) {
    views t: cstr_at(s, _);
    requires n == t.len;
    ensures result == t.len;
} by {
    execute();
    simp();
}

uint64 measure(const uint8* src, uint64 m) {
    views cstr_at(src, m);
    ensures result == m;
} by {
    execute();
    simp();
}
```

```expect
pass
```
