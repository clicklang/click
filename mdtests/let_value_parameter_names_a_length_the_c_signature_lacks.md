# `let n: T;` declares a contract value the C signature lacks

A function contract can state a value its C signature does not carry with
`let n: T;`. Here `measure` views a string of some length `n` and returns it.
`n` is a value parameter of the contract: nothing is passed at run time, and
a call takes it from the one held `cstr_at(s, _)` instance. The caller `g`
declares its own `m` the same way, so its view supplies `measure`'s `n`.

```c filename=let_value_parameter_names_a_length_the_c_signature_lacks.c
unsigned long measure(const char *s);

unsigned long g(const char *s)
{
	return measure(s);
}
```

```click
import click::cstr;
verifying "let_value_parameter_names_a_length_the_c_signature_lacks.c";

extern uint64 measure(const char* s) {
    let n: uint64;
    views cstr_at(s, n);
    ensures result == n;
}

uint64 g(const char* s) {
    let m: uint64;
    views cstr_at(s, m);
    ensures result == m;
} by {
    execute();
    simp();
}
```

```expect
pass
```
