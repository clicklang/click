# Saved struct pointer elements keep their stride

```c filename=saved_struct.c
struct pair { int first; int second; };
void advance(struct pair *p, struct pair *q, unsigned long i) { p = q; i++; }
```

```click
import click::separation;
verifying "saved_struct.c";
void advance(struct pair *p, struct pair *q, uint64 i) {
    ensures true;
    requires i == 0;
} by {
    step();
    step();
    have i != 0;
    have separate(memory(old(p)[i]), memory(old(p)[0])) by {
        apply(separation::elements(old(p), i, 0u64)) using { i != 0; };
    }
    step();
}
```

```expect
pass
```
