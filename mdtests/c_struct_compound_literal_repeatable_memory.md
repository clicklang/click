# Compound literal boundary: repeatable memory

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = 0; while ((p = &(struct pair){ .left = p ? p->left + 1 : 20 })->left < 30) { return 0; } return 0; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 20; }
```

```expect
fail: repeatable loop-clause compound literal initializers
```
