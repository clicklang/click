# `step({ ... })` names only binders the frontier callee declares

`step({ ... })` takes its callee from the call at the frontier, so its entries
are checked against that callee's contract when the step runs. This
`snprintf`'s only `%s` converts argument 1, so its one value binder is `s1`.
An entry for `s0` is refused and names the call.

```c filename=step_value_map_names_a_binder_the_callee_lacks.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int f(char *buf, int len)
{
	char tmp[12];

	tmp[0] = '\0';
	return snprintf(buf, len, "%u%s", (unsigned int)7, tmp);
}
```

```click
import click::cstr;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "step_value_map_names_a_binder_the_callee_lacks.c";

int32 f(char buf[], int32 len) {
    requires 9 <= len;
    owns buf[0..(uint64) len];
    ensures result >= 0;
} by {
    step();
    step();
    step({ s0: cstr_at(tmp, 0u64) });
    execute();
}
```

```expect
fail: `snprintf` with format "%u%s" declares no value binder `s0`
```
