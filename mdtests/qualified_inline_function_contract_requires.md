# A qualified inline contract is enforced at its own call sites

```c filename=first.c
static inline int helper(int x) { return x; }
int run(void) { return helper(-1); }
```

```c filename=second.c
static inline int helper(int x) { return x; }
int other(int x) { return helper(x); }
```

```click
verifying "first.c" as first;
verifying "second.c" as second;
int32 first::helper(int32 x) {
    requires x >= 0;
    ensures result == x;
} by { execute(); simp(); }
int32 run() { ensures result == -1; } by { execute(); simp(); }
```

```expect
fail: precondition clause 1 of `helper#inline:first.c`
```
