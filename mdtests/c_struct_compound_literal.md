# A block-scope C99 compound literal

```c filename=example.c
struct pair { int left; int right; };

int answer(void) {
    struct pair *p = &(struct pair){ 20, 22 };
    return p->left + p->right;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
