# Reject invalid or unmodeled compound literal use: initializer order

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { int i = 0; struct pair *p = &(struct pair){i++, i++}; return p->left; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 20; }
```

```expect
fail: initializer evaluations with interacting side effects
```
