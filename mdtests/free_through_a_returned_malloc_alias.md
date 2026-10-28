# A returned alias still names the allocated object

```c filename=free_returned_alias.c
int32* identity(int32* p) { return p; }
void dispose(void) {
    int32* p = malloc(4);
    if (p == 0) return;
    int32* q = identity(p);
    free(q);
}
```

```click
verifying "free_returned_alias.c";
int32* identity(int32* p) { ensures result == p; }
void dispose() { ensures true; }
```

```expect
pass
```
