# A character literal holds one byte

```c filename=c_multibyte_character_literal_rejected.c
int32 value(void) {
    return '\0011';
}
```

```click
verifying "c_multibyte_character_literal_rejected.c";

int32 value() {
    ensures true by auto;
}
```

```expect
fail:c_multibyte_character_literal_rejected.c:2: character literals must contain exactly one byte
```
