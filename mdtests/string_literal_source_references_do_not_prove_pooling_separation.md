# Source occurrence identities do not force distinct storage

```c filename=literal_pooling.c
const char* text(int choose) { if (choose) return "same"; return "same"; }
```

```click
verifying "literal_pooling.c";
const char* text(int32 choose) {
    ensures text.string_literal(0) != text.string_literal(1);
}
```

```expect
fail: unclosed goal
```
