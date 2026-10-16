# A record-pointer identity call preserves access to caller-local storage

```c filename=identity.c
struct Pair { int first; int second; };
struct Pair *identity(struct Pair *pair) { return pair; }
int caller(void) {
    struct Pair pair = { 7, 9 };
    struct Pair *q = identity(&pair);
    return q->first;
}
```

```click
verifying "identity.c";
struct Pair* identity(struct Pair* pair) {
    views pair->first;
    ensures result == pair;
} by { execute(); simp(); }
int32 caller() {
    ensures result == 7;
} by { execute(); simp(); }
```

```expect
pass
```
