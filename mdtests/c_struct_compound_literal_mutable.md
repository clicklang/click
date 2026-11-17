# Block-scope struct compound literal: mutable

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = &(struct pair){20, 22}; p->left = 21; int right = p->right; return p->left + right; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 43; }
```

```expect
pass
```
