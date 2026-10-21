# `step({ ... })` maps the value binders of the call at the frontier

A call step that only names a callee's value binders is written `step({ ... })`.
The callee and its arguments come from the call at the frontier, so the proof
never restates them. That matters here: the call passes
`(flags & 1) ? "" : " "`, which a proof expression cannot write.

The map gives the `%s` of argument 0, binder `s0`, the string the local array
`tmp` holds: `cstr_at(tmp, 0u64)`. The entry supplies only `s0`'s length. The
`%s` of argument 1 takes the view of whichever string literal the condition
selects, so the call has one successor per value of `flags & 1`.

```c filename=step_value_map_takes_the_frontier_call.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int f(char *buf, int len, unsigned int flags)
{
	char tmp[12];

	tmp[0] = '\0';
	return snprintf(buf, len, "%s%s", tmp, (flags & 1) ? "" : " ");
}
```

```click
import click::cstr;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "step_value_map_takes_the_frontier_call.c";

int32 f(char buf[], int32 len, uint32 flags) {
    requires 9 <= len;
    owns buf[0..(uint64) len];
    ensures result <= 1;
} by {
    step();
    step();
    if (flags & 1u32) != 0u32 {
        step({ s0: cstr_at(tmp, 0u64) });
        execute();
        simp();
    } else {
        let { result: count } = step({ s0: cstr_at(tmp, 0u64) });
        execute();
        simp();
    }
}
```

```expect
pass
```
