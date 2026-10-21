# A function with a value parameter is proved for every value

`known_length`'s contract declares the string's length as a value parameter,
`let k: uint64;`, so its body is proved at an arbitrary `k`: the requirement
`n == k` and the postcondition both name it, and the proof never fixes it.
The caller takes the length from the string it holds. The owning form is
[`cstr_at_owned_value_parameter_keeps_its_length.md`](cstr_at_owned_value_parameter_keeps_its_length.md).

```c filename=cstr_at_value_parameter_is_proved_for_every_length.c
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

verifying "cstr_at_value_parameter_is_proved_for_every_length.c";

uint64 known_length(const uint8* s, uint64 n) {
    let k: uint64;
    views cstr_at(s, k);
    requires n == k;
    ensures result == k;
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
