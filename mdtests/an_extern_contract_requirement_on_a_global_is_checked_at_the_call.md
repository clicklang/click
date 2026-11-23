# An `extern` contract's requirement on a C global is checked at the call

The requirement reads `counter` at the call, where it holds `2`, so the
call is refused.

```c filename=an_extern_contract_requirement_on_a_global_is_checked_at_the_call.c
int counter;
void check(void);

void caller(void)
{
    counter = 2;
    check();
}
```

```click
verifying "an_extern_contract_requirement_on_a_global_is_checked_at_the_call.c";

extern void check() {
    requires counter == 1;
    ensures true;
}

void caller() {
    owns counter;
    ensures true;
} by {
    step();
    step();
}
```

```expect
fail:unproved obligation
```
