# C fragments in contracts

This checks the C-fragment contract clauses shown in the C fragments concept
page: C integer arithmetic, `viewable` ranges, and `old(...)` memory reads.

```c filename=c_fragments.c
int32 c_fragments(int32 x, int32 p[], int32 n, int32 k) {
    return x + 1;
}
```

```click
verifying "c_fragments.c";

int32 c_fragments(int32 x, int32 p[], int32 n, int32 k) {
    requires x < 2147483647;
    requires n >= 1;
    requires 0 <= k and k < n;
    requires viewable(p[0..n]);
    ensures result == x + 1 by auto();
    ensures p[k] == old(p[k]) by auto();
    ensures p[0] == old(p[0]) by auto();
}
```

```expect
pass
```
