# Exact and typed reads of fixed-offset local cells

A write to a sibling field leaves the ordinary read versions intact.
An exact read names the selected point. The stored Boolean can be proved
from its write, and the complete pointer values still support the final
indirect call and dereference.

```c filename=typed.c
struct Values {
    int32 integer;
    _Bool flag;
    int32 *pointer;
    int32 (*callback)(void);
    int32 sibling;
};
int32 answer(void) { return 42; }

int32 check(int32 *p, _Bool flag) {
    struct Values values;
    values.integer = 9;
    values.flag = flag;
    values.pointer = p;
    values.callback = answer;
    values.sibling = 1;
    int32 result = values.callback();
    return result + *values.pointer;
}
```

```click
verifying "typed.c";
int32 answer() { ensures result == 42; }

int32 check(int32 *p, Bool flag) {
    owns *p;
    requires *p == 0;
    ensures result == 42;
} by {
    step(); step(); step(); step(); step();
    mark written;
    step();
    have exact(values.integer) == at(written, exact(values.integer)) by close();
    have values.flag == flag by close();
    have exact(values.flag) == values.flag by close();
    have values.flag == at(written, values.flag) by close();
    have values.pointer == p;
    have exact(values.pointer) == values.pointer by close();
    have exact(values.callback) == values.callback by close();
    have values.pointer == at(written, values.pointer) by close();
    have values.callback == at(written, values.callback) by close();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
