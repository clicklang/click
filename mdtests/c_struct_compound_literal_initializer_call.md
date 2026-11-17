# A call in a compound literal initializer is evaluated at the literal

```c filename=example.c
struct pair { int left; int right; };
int identity(int value) { return value; }
int answer(void) {
    struct pair *p = &(struct pair){identity(20), 22};
    return p->left + p->right;
}
```

```click
verifying "example.c";
int32 identity(int32 value) { ensures result == value; }
int32 answer() { ensures result == 42; }
```

```expect
pass
```
