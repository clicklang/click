# Untouched static integer elements retain their function-entry version

```c filename=static_elements.c
int32 values[8];
uint16 halves[8];
uint64 words[8];

int32 read_value(int32 i) { return values[i]; }
uint16 read_half(int32 i) { return halves[i]; }
uint64 read_word(int32 i) { return words[i]; }
```

```click
verifying "static_elements.c";

int32 read_value(int32 i) {
    requires 0 <= i;
    requires i < 8;
    ensures result == old(values[i]);
}
uint16 read_half(int32 i) {
    requires 0 <= i;
    requires i < 8;
    ensures result == old(halves[i]);
}
uint64 read_word(int32 i) {
    requires 0 <= i;
    requires i < 8;
    ensures result == old(words[i]);
}
```

```expect
pass
```
