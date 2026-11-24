# A call's requirement on a value parameter reads the caller's value parameter

`take` declares its string's length as a value parameter, `let n: uint64;`,
and requires `n <= 100u64`. At the call, `n` takes the length of the
`cstr_at` instance the caller views, which is the caller's own value
parameter `m`. The requirement is then `m <= 100u64`, which the caller
states. The implicit proof names `m` as the caller's parameter, since a
contract value parameter has no local in the execution state.

```c filename=a_call_requirement_on_a_value_parameter_reads_the_callers_value_parameter.c
unsigned long take(const unsigned char *s);

unsigned long caller(const unsigned char *message)
{
    return take(message);
}
```

```click
verifying "a_call_requirement_on_a_value_parameter_reads_the_callers_value_parameter.c";
import click::c::string::{cstr_at};

extern uint64 take(const uint8* s) {
    let n: uint64;
    views cstr_at(s, n);
    requires n <= 100u64;
    ensures result == n;
}

uint64 caller(const uint8* message) {
    let m: uint64;
    views cstr_at(message, m);
    requires m <= 100u64;
    ensures result == m;
}
```

```expect
pass
```
