# Explicit C indices retain their binding
```c filename=zero.c
struct object { int32 values[2][2]; };
int32 zero(int32 result, struct object* p) { return 0; }
```
```click
verifying "zero.c";
int32 zero(int32 result, struct object* p) {
    views p->values[0][0];
    views p->values[1][0];
    requires c(result) == 1;
    requires p->values[0][0] == 3 and p->values[1][0] == 7;
    ensures p->values[c(result)][0] == 3 by auto;
}
```
```expect
fail: unclosed goal
```
