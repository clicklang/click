# Symbolic struct range
```c filename=sn.c
struct pt { int32 x; int64 y; };
int64 at(struct pt *p, int32 n, int32 i) { return p[i].y; }
```
```click
verifying "sn.c";
int64 at(struct pt* p, int32 n, int32 i) {
 requires 0 <= i;
 requires i <= n;
 views p[0..n];
 ensures result == p[i].y;
} by { execute(); simp(); }
```
```expect
fail: missing resource fact `views p[i].y`
```
