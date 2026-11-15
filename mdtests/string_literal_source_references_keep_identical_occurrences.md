# Equal text does not collapse source occurrence references

```c filename=literal_occurrences.c
const char* text(int choose) { if (choose) return "same"; return "same"; }
```

```click
verifying "literal_occurrences.c";
const char* text(int32 choose) {
    ensures result == text.string_literal(0) or result == text.string_literal(1);
}
```

```expect
pass
```
