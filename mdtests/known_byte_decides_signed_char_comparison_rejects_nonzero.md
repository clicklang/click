# A nonzero byte does not satisfy a zero comparison

```c filename=first_is_nul.c
int first_is_nul(char *p) {
    return p[0] == '\0';
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "first_is_nul.c";
int32 first_is_nul(char* p) {
    views p[0..1];
    requires ((uint8*)p)[0] == 1;
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: unclosed goal
```
