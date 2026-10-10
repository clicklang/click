# Automatic scalar allocation ownership reaches a modular helper

The declaration supplies exact byte ownership. A verified helper borrows it,
writes the scalar, and returns the permission and its new value. No extra
ownership annotation is needed in the caller.

```c filename=scalar.c
void fill(uint32* p, uint32 value) { *p = value; }
uint32 probe(uint32 value) {
    uint32 obj = 0;
    fill(&obj, value);
    return obj;
}
```

```click
verifying "scalar.c";
void fill(uint32* p, uint32 value) {
    owns p[0..1];
    ensures p[0] == value;
} by { execute(); simp(); }
uint32 probe(uint32 value) {
    ensures result == value;
} by { execute(); simp(); }
```

```expect
pass
```
