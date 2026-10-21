# A call map value for a value binder is refused

`measure`'s `str` is a value binder: its entry names the instance whose
`cstr_at` argument gives `str.len`, `{ str: cstr_at(tmp, 0u64) }`. A bare
value, `{ str: 0u64 }`, names no instance, so the step is refused with the
form to write. A value is written for a `let` value parameter instead
(`step_value_map_gives_a_let_parameter_its_value.md`).

```c filename=step_value_map_value_for_a_value_binder_is_refused.c
unsigned long measure(const char *s);

unsigned long f(void)
{
	char tmp[12];

	tmp[0] = '\0';
	return measure(tmp);
}
```

```click
import click::cstr;
verifying "step_value_map_value_for_a_value_binder_is_refused.c";

extern uint64 measure(const char* s) {
    views str: cstr_at(s, _);
    ensures result == str.len;
}

uint64 f() {
    ensures result == 0u64;
} by {
    step();
    step();
    step({ str: 0u64 });
    execute();
    simp();
}
```

```expect
fail: `str` is a value binder of `measure`; map it to a resource term such as `str: cstr_at(p, n)`
```
