# Compound literal boundary: unbraced expired

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = 0; if (1) p = &(struct pair){20,22}; return p->left; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 20; }
```

```expect
fail: invalid memory access
```
