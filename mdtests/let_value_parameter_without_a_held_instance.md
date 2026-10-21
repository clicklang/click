# A `let` value parameter with no held instance names the map entry

`measure` takes `n` from a held `cstr_at(s, _)` instance. The caller holds
none for the local array `tmp`, so plain `step()` is refused, and the message
names the entry that supplies the value instead, `step({ n: value })`.

```c filename=let_value_parameter_without_a_held_instance.c
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
verifying "let_value_parameter_without_a_held_instance.c";

extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 f() {
    ensures result == 0u64;
} by {
    step();
    step();
    step();
    execute();
    simp();
}
```

```expect
fail: or give the value with `step({ n: value })`
```
