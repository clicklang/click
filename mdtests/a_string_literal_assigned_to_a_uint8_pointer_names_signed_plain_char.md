# A string literal assigned to a `uint8 *` names signed plain `char`

The assignment form of
`a_string_literal_initializing_a_uint8_pointer_names_signed_plain_char.md`:
under the default x86_64-linux-userspace target, assigning a string literal to
a `uint8 *` local without a cast is refused with the conversion named, not a
generic type mismatch.

```c filename=a_string_literal_assigned_to_a_uint8_pointer_names_signed_plain_char.c
uint8* string_literal_assignment() {
    uint8* message;
    message = "ok";
    return message;
}
```

```click
verifying "a_string_literal_assigned_to_a_uint8_pointer_names_signed_plain_char.c";

uint8* string_literal_assignment() {
    ensures result != 0;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer signedness mismatch: `char *` (plain `char` is signed on x86_64-linux-userspace) is converted to `uint8 *` without a cast; cast it with `(uint8 *)` or use `char *`
```
