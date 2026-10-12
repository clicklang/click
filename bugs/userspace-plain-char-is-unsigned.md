# The userspace target models plain `char` as unsigned

## Violated invariant

A claim verified under `target "x86_64-linux-userspace";` holds for that
platform as built by its default toolchain. The x86-64 System V ABI, and gcc
and clang on x86-64 Linux by default, make plain `char` signed. Click's
userspace target treats it as unsigned and predefines `__CHAR_UNSIGNED__`, so
it verifies claims that are false for an ordinary user-space build.

The kernel target is correct as is: Linux builds with `-funsigned-char`.

## Reproduction

`c.c`:

```c
int high_char_is_negative(void) {
    char c = (char)200;
    return c < 0;
}
```

`c.click`:

```click
target "x86_64-linux-userspace";
verifying "c.c";

int32 high_char_is_negative() {
    ensures result == 0 by auto;
}
```

`click verify c.click` reports `1 selected proof verified`. Built with the
system gcc on x86-64 Linux, the function returns 1, and `gcc -dM -E` does not
define `__CHAR_UNSIGNED__`.

The unsigned choice is deliberate in the code: `CTarget::plain_char_is_signed`
in `src/languages/c/target.rs` returns false for both targets,
`C0Type::to_kernel_type` in `src/languages/c/syntax.rs` maps `Char` to
`UInt8`, and `src/surface/validation/type_validation.rs` asserts at compile
time that no target has signed plain `char`, because C strings are passed to
specifications as `uint8` bytes.

## Acceptance criteria

- Under the userspace target, plain `char` has signed 8-bit values,
  `__CHAR_UNSIGNED__` is not predefined, and the reproduction verifies
  `result == 1` and refuses `result == 0`.
- Under the kernel target, the reproduction still verifies `result == 0`.
- C strings, `char *` parameters, string literals, and the prelude's string
  functions keep working under both targets, with a stated rule for how a
  `char` byte reaches a specification.
- mdtests cover both targets, and `docs/reference/language/c0.md` and
  `docs/concepts/trust.md` describe each target's plain `char`.
