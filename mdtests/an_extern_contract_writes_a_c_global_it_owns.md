# An `extern` contract writes a C global it owns

An `extern` contract that owns a global may state the value the call leaves
in it, as a verified function's contract does.

```c filename=an_extern_contract_writes_a_c_global_it_owns.c
int counter;
void bump(void);

void caller(void)
{
    counter = 1;
    bump();
}
```

```click
verifying "an_extern_contract_writes_a_c_global_it_owns.c";

extern void bump() {
    owns counter;
    ensures counter == old(counter) + 1;
}

void caller() {
    owns counter;
    ensures counter == 2;
} by {
    step();
    step();
}
```

```expect
pass
```
