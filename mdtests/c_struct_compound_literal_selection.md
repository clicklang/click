# A literal in an if condition remains live through its selected body

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    struct pair *p = 0;
    if ((p = &(struct pair){20,22})->left == 20) {
        return p->left + p->right;
    }
    return 0;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 42; }
```

```expect
pass
```
