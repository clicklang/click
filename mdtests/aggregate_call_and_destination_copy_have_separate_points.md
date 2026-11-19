# An aggregate call returns before its destination is copied

The original C assignment has a call endpoint and a later destination-copy
endpoint. The callee mutates the destination, then the copy overwrites it.

```c filename=aggregate_destination.c
struct pair { int x; int y; };
struct pair replace(struct pair *p) {
    p->x = 7;
    struct pair result = {3, 4};
    return result;
}
int caller(void) {
    struct pair p = {0, 0};
    p = replace(&p);
    return p.x;
}
```

```click
verifying "aggregate_destination.c";
struct pair replace(struct pair *p) {
    owns p->x;
    ensures p->x == 7;
    ensures result.x == 3;
    ensures result.y == 4;
}
int32 caller() {
    ensures result == 3;
} by {
    step_until(statement(1).call(0));
    step();
    have at(statement(1).call(0).exit, p.x == 7) by { known(); }
    have load<int32>(statement(1).call(0).result) == 3 by { known(); }
    step();
    have at(statement(1).assignment(p, 0).exit, p.x == 3) by { known(); }
    step_until(function.exit);
    known();
}
```

```expect
pass
```
