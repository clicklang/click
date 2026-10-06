# Array indices distinguish C bindings from contract returns
```c filename=zero.c
struct object { int32 values[2][2]; int32 single[2]; };
int32 zero(int32 result, struct object* p) { return 0; }
```
```click
verifying "zero.c";
int32 zero(int32 result, struct object* p) {
    views p->values[0][0];
    views p->values[1][0];
    views p->single[1..2];
    requires c(result) == 1;
    requires p->values[0][0] == 3 and p->values[1][0] == 7;
    requires p->single[1] == 9;
    ensures p->values[c(result)][0] == 7 by auto;
    ensures old(p)->values[c(result)][0] == 7 by auto;
    ensures p->values[c(result) + result][0] == 7 by auto;
    ensures p->values[result][0] == 3 by auto;
    ensures p->single[c(result)] == 9 by auto;
}
```
```expect
pass
```
