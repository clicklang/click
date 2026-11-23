# An `extern` contract reads a C global at the call

An `extern` contract may name the program's externally linked file-scope
objects, as a verified function's contract does. A requirement reads the
global's value at the call, like a parameter's, so the caller proves it
there.

```c filename=an_extern_contract_reads_a_c_global.c
int counter;
void check(void);

void caller(void)
{
    counter = 1;
    check();
}
```

```click
verifying "an_extern_contract_reads_a_c_global.c";

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
pass
```
