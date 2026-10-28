# Free accepts a proven alias of an owned allocation base

```c filename=free_alias.c
void dispose(int32* p, int32* q) { free(q); }
```

```click
verifying "free_alias.c";
void dispose(int32* p, int32* q) {
    consumes allocation(p, 4);
    consumes p[0..1];
    requires q == p;
} by {
    have q == p by { assumption(); }
    step();
}
```

```expect
pass
```
