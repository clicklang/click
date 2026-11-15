# Literal owners with equal function names are qualified by source

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
    ensures result == first::text.string_literal(0);
}
const char* second::text() {
    ensures result == "literal_second.c"::text.string_literal(0);
}
```

```expect
pass
```
