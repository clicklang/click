# Block-scope struct compound literal: designated

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = &(struct pair){ .right = 42 }; return p->left + p->right; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
