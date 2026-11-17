# Compound literal typedef

```c filename=example.c
struct pair { int left; int right; }; typedef struct pair Pair; int answer(void) { Pair *p = &(Pair){20, 22}; return p->left + p->right; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
