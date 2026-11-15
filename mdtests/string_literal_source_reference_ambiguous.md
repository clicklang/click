# Literal owners with equal function names require source qualification

```c filename=literal_first.c
static inline const char* text() { return "first"; }
```

```c filename=literal_second.c
static inline const char* text() { return "second"; }
```

```click
verifying "literal_first.c" as first;
verifying "literal_second.c" as second;
const char* first::text() {
    ensures result == text.string_literal(0);
}
```

```expect
fail: literal owner `text` is ambiguous
```
