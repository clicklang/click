# Symbolic struct range
```c filename=sn.c
struct pt { int32 x; int64 y; };
int64 first(struct pt *p, int32 n) { return p[0].y; }
```
```click
verifying "sn.c";
int64 first(struct pt* p, int32 n) {
 requires n >= 1;
 views p[0..n];
 ensures result == p[0].y;
} by { execute(); simp(); }
```
```expect
pass
```
