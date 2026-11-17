# Block-scope struct compound literal: gnu scope

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { return ({ struct pair *p = &(struct pair){20, 22}; p->left + p->right; }); }
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
