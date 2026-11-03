# Mirrored implication consequents close the same contradiction

Both contracts state the same bound. Introducing the nonzero premise exposes
an order fact that contradicts the upper bound, regardless of orientation.

```c filename=mirrored.c
unsigned int direct(unsigned int x) { return 0; }
unsigned int mirrored(unsigned int x) { return 0; }
```

```click
verifying "mirrored.c";
uint32 direct(uint32 x) {
    requires x != 0u32 implies x > 100u32;
    requires x <= 100u32;
    ensures x != 0u32 implies x <= 100u32 implies result == x;
}
uint32 mirrored(uint32 x) {
    requires x != 0u32 implies 100u32 < x;
    requires x <= 100u32;
    ensures x != 0u32 implies x <= 100u32 implies result == x;
}
```

```expect
pass
```
