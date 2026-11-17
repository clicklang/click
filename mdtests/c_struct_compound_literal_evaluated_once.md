# Block-scope struct compound literal: evaluated once

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { int count = 0; struct pair *p = &(struct pair){count++, 22}; return p->left + p->right + count; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 23; }
```

```expect
pass
```
