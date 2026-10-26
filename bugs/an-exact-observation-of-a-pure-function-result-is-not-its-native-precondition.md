# An exact observation of a pure function's result is not its native precondition

Soundness: incomplete. A provable call is refused; nothing false verifies.

## Violated invariant

A comparison of exact observations is the native comparison it observes
(`docs/reference/language/index.md`, Integer specification arithmetic):
`to_integer(f(a)) <= 2147483647` and `f(a) <= 2147483647u64` are one fact. The
precondition discharge in the implicit tail proves the native spelling of an
`extern` requirement over a library pure function's `uint64` result, but not
the exact-observation spelling, with or without Integer-default arithmetic.

## Reproduction

```c
int take(unsigned int a);
int native_call(void) { return take(123u); }
```

```click
import click::format;
verifying "call.c";
extern int32 take(uint32 a) {
    requires to_integer(click::format::decimal_length((uint64) a)) <= 2147483647;
    ensures result == 0;
}
int32 native_call() {
    ensures result == 0;
}
```

The implicit tail refuses: "condition-certificate premise search did not derive
`click::format::decimal_length(123u64) <= 2147483647u64` from 1 ambient
condition facts". The same file with
`requires click::format::decimal_length((uint64) a) <= 2147483647u64;`
verifies.

The generated `snprintf` contract (`src/languages/c/formatted_output.rs`)
avoids this by stating a single variable length with no arithmetic; a format
with two or more conversions states an Integer sum and may hit the same gap.

## Acceptance

- Both spellings of the reproduction verify.
- A regression mdtest keeps the exact-observation spelling.
