# Compound literal boundary: goto

```c filename=example.c
struct pair { int left; int right; };
int answer(void) { struct pair *p = &(struct pair){20,22}; goto out; out: return p->left; }
```

```click
verifying "example.c";
int32 answer() { ensures result == 20; }
```

```expect
fail: compound literals and goto
```
