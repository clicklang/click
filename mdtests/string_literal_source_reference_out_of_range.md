# A missing source literal is refused

```c filename=missing_literal.c
const char* text() { return "hello"; }
```

```click
verifying "missing_literal.c";
const char* text() {
    ensures result == text.string_literal(1);
}
```

```expect
fail: unknown string literal
```
