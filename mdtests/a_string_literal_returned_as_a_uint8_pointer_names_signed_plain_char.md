# A string literal returned as `uint8 *` names signed plain `char`

Under the default x86_64-linux-userspace target, plain `char` is signed, so a
string literal's `char *` and `uint8 *` point to character types of different
signedness (C11 6.5.16.1p1; GCC's `-Wpointer-sign`). Returning the literal
without a cast is refused, and the refusal names the conversion, plain
`char`'s signedness on the target, and the cast that fixes it rather than a
generic return-type mismatch. Under x86_64-linux-kernel, where plain `char` is
unsigned, the same function verifies; see `string_literals.md`.

```c filename=a_string_literal_returned_as_a_uint8_pointer_names_signed_plain_char.c
uint8* string_literal() {
    return "ok";
}
```

```click
verifying "a_string_literal_returned_as_a_uint8_pointer_names_signed_plain_char.c";

uint8* string_literal() {
    ensures readable: viewable(result[0..3]);
} by {
    execute();
    simp();
}
```

```expect
fail: pointer signedness mismatch: `char *` (plain `char` is signed on x86_64-linux-userspace) is converted to `uint8 *` without a cast; cast it with `(uint8 *)` or use `char *`
```
