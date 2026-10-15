# A known zero byte does not decide a signed `char` comparison

Soundness: incomplete. Click refuses a true postcondition: the program is
correct and nothing false is accepted. The refused step is a comparison whose
outcome the unsigned byte fact already decides.

The [byte-representation note](../docs/internals/byte-representation.md#character-reads-of-one-byte-cells)
says constant facts cross the signed-read conversion forward: a known byte
`u == c` folds `int8(u)` to its two's-complement value wherever a term's
constant is computed. That holds for a returned value (`return p[0];` with
`((uint8*)p)[0] == 0` proves `result == 0`), but not for the branch that a
comparison of the same read opens: with the same fact, the path whose case is
`(int8)old(*p) != 0` is not refuted, so `return p[0] == '\0';` cannot be
shown to return 1.

This blocks reading a C string's terminator through plain `char` after
`cstr::readable_len(src, n)`, or after opening the library's
`cstr_at(src, n)`, whose facts state the bytes through `(uint8*)src`.

## Reproduction

```c filename=first_is_nul.c
int first_is_nul(char *p) {
    return p[0] == '\0';
}
```

```click
target "x86_64-linux-userspace";
verifying "first_is_nul.c";

int32 first_is_nul(char* p) {
    views p[0..1];
    requires ((uint8*)p)[0] == 0;
    ensures result == 1;
} by {
    execute();
    simp();
}
```

Observed (master at 765ede18 plus the `cstr_at` library export):

```text
`ensures result == 1` failed for `first_is_nul.ensures_0` path 1
unclosed goal
result == 1; left side evaluated to 0, right side evaluated to 1
case: [(int8)old(*p) != 0]
```

The same failure occurs with `requires cstr::readable_len(src, n);`,
`unfold(cstr::readable_len)` and `return src[n] == '\0';`, and inside
`open(cstr_at(src, n)) { ... }`. With `const uint8*` in place of `char*`
each version verifies.

## Acceptance criteria

- The reproduction verifies as an mdtest, keeping the plain-`char` source
  pattern `return p[0] == '\0';`.
- A negative twin with `requires ((uint8*)p)[0] == 1;` still fails.
- A symbolic-index version through `cstr_at(src, n)` and
  `return src[n] == '\0';` verifies.
