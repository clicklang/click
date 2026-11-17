# Const compound literals require immutable aggregate construction

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    const struct pair *p = &(const struct pair){20, 22};
    struct pair *q = (struct pair*)p;
    q->left = 21;
    return q->left;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 21; }
```

```expect
fail: const-qualified struct compound literals require immutable aggregate storage
```
