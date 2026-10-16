# A union member read after a store to another member is allowed

GCC documents reading a union member other than the one last written as
defined. A struct's class admits the class of every member of a union it
contains, so a `long long` member read after a store through the `long`
member's pointer verifies.

```c filename=union.c
union wide { long l; long long ll; };
struct tagged { int tag; union wide u; };

long long punned(void) {
    struct tagged s;
    long *lp = &s.u.l;
    *lp = 7;
    return s.u.ll;
}
```

```click
verifying "union.c";

long long punned() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
