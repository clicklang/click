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
    requires program::result == 1;
    requires p->values[0][0] == 3 and p->values[1][0] == 7;
    requires p->single[1] == 9;
    ensures p->values[program::result][0] == 7;
    ensures old(p)->values[program::result][0] == 7;
    ensures p->values[program::result + result][0] == 7;
    ensures p->values[result][0] == 3;
    ensures p->single[program::result] == 9;
} by {
    step();
    have p->values[program::result][0] == 7 by {
        rewrite(program::result, 1);
        close();
    }
    have old(p)->values[program::result][0] == 7 by {
        rewrite(program::result, 1);
        close();
    }
    have p->values[program::result + result][0] == 7 by {
        rewrite(program::result, 1);
        close();
    }
    have p->values[result][0] == 3 by { close(); }
    have p->single[program::result] == 9 by {
        rewrite(program::result, 1);
        close();
    }
    close();
}
```
```expect
pass
```
