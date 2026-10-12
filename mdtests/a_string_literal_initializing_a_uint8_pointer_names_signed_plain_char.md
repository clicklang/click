# A string literal initializing a `uint8 *` names signed plain `char`

Under the default x86_64-linux-userspace target, plain `char` is signed, so
initializing a `uint8 *` local from a string literal without a cast converts
between pointers to character types of different signedness (C11 6.5.16.1p1;
GCC's `-Wpointer-sign`). The refusal names that conversion, plain `char`'s
signedness on the target, and the cast that fixes it rather than a generic
type mismatch.

```c filename=a_string_literal_initializing_a_uint8_pointer_names_signed_plain_char.c
int32 string_literal_initializer() {
    uint8* first = "ok";
    return first[0] == 'o';
}
```

```click
verifying "a_string_literal_initializing_a_uint8_pointer_names_signed_plain_char.c";

int32 string_literal_initializer() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer signedness mismatch: `char *` (plain `char` is signed on x86_64-linux-userspace) is converted to `uint8 *` without a cast; cast it with `(uint8 *)` or use `char *`
```
