# Block-scope struct compound literal: conditional

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { int count = 0; struct pair *p = 1 ? &(struct pair){++count, 2} : &(struct pair){++count, 9}; return count + p->left + p->right; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 4; }
```

```expect
pass
```
