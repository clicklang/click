# A variadic contract may name a value

A contract's `let` value is a parameter after `...args`, so a variadic
contract may name one, here the length of its C string format.

```c filename=a_variadic_contract_may_name_a_value.c
unsigned long measure(const char *format, ...);

unsigned long run(void)
{
    return measure("abc", 1);
}
```

```click
verifying "a_variadic_contract_may_name_a_value.c";

extern uint64 measure(const uint8* format, ...args) {
    let n: uint64;
    views click::c::string::cstr_at(format, n);
    ensures result == n;
}

uint64 run() {
    ensures result == 3u64;
}
```

```expect
pass
```
