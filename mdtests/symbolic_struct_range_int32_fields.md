# Symbolic ranges count struct objects

```c filename=sn.c
struct pt { int x; int y; };
int first(struct pt *p, int n) { return p[0].y; }
int at(struct pt *p, int n, int i) { return p[i].y; }
```

```click
verifying "sn.c";

int32 first(struct pt* p, int32 n) {
    requires n >= 1;
    views p[0..n];
    ensures result == p[0].y;
} by { execute(); simp(); }

int32 at(struct pt* p, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    views p[0..n];
    ensures result == p[i].y;
} by { execute(); simp(); }
```

```expect
pass
```
