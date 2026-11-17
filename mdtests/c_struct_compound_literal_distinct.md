# Block-scope struct compound literal: distinct

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = &(struct pair){1, 2}; struct pair *q = &(struct pair){3, 4}; p->left = 9; return p->left + q->left; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 12; }
```

```expect
pass
```
