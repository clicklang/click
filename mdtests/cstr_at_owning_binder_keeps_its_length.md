# An owning binder keeps its length

`keep` owns its string, `owns k: cstr_at(p, _);`. The `_` is a value
parameter of the contract, and an `owns` clause returns the instance it
received, so `old(k.len)` and the length at exit are the same value. The
body is proved for every length; `measure` takes the length from the string
it owns. The viewing form is
[`cstr_at_binder_length_is_proved_for_every_length.md`](cstr_at_binder_length_is_proved_for_every_length.md).

```c filename=cstr_at_owning_binder_keeps_its_length.c
uint64 keep(uint8 *p, uint64 n)
{
	return n;
}

uint64 measure(uint8 *src, uint64 m)
{
	return keep(src, m);
}
```

```click
import click::cstr;

verifying "cstr_at_owning_binder_keeps_its_length.c";

uint64 keep(uint8* p, uint64 n) {
    owns k: cstr_at(p, _);
    requires n == k.len;
    ensures result == old(k.len);
} by {
    execute();
    simp();
}

uint64 measure(uint8* src, uint64 m) {
    owns cstr_at(src, m);
    ensures result == m;
} by {
    execute();
    simp();
}
```

```expect
pass
```
