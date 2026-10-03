# Unknown escapes stay rejected

```c filename=c_unknown_character_escape_rejected.c
int32 value(void) {
    return '\q';
}
```

```click
verifying "c_unknown_character_escape_rejected.c";

int32 value() {
    ensures true by auto;
}
```

```expect
fail:c_unknown_character_escape_rejected.c:2: unsupported character escape `\q`
```
