# A compound literal can be passed directly to a viewed struct parameter

```c filename=example.c
struct pair { int left; int right; };
int sum(const struct pair *p) { return p->left + p->right; }
int answer(void) { return sum(&(struct pair){20, 22}); }
```

```click
verifying "example.c";
int32 sum(const struct pair* p) {
    views p->left;
    views p->right;
    requires 0 <= p->left and p->left <= 100;
    requires 0 <= p->right and p->right <= 100;
    ensures result == p->left + p->right;
}
int32 answer() { ensures result == 42; }
```

```expect
pass
```
