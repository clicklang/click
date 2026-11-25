# A by-value struct argument is spelled by its call's parameter

`first` takes `struct pair` by value. Before the call, the argument is copied
into the callee's parameter object, in regions of their own: the object is
allocated, then `q` is copied into it. So `return first(q);` takes two steps
before the step that runs the call, and the callee's contract reads the copy
at the call's entry: the requirement `p.a <= 1000u32` is about the copy. The
caller has no local naming the copy.

The call names the copy: a call's region has, for each by-value aggregate
parameter, `.parameter(name)`, the object the call receives, read like a
local in the current state. The step that runs the call starts at the call's
entry, so it writes its requirement as
`statement(3).call(first, 0).parameter(p).a <= 1000u32`, which lowers to the
very obligation the call leaves open, and proves it from the caller's own
facts. The object's lifetime ends when the call returns, so after the call its
value is read at the call's entry, here as `x`.

```c filename=by_value_parameter.c
struct pair { uint32 a; uint32 b; };

uint32 first(struct pair p) {
    return p.a;
}

uint32 caller(uint32 x) {
    struct pair q;
    q.a = x;
    q.b = 2;
    return first(q);
}
```

```click
verifying "by_value_parameter.c";

uint32 first(struct pair p) {
    requires p.a <= 1000u32;
    ensures result == p.a;
}

uint32 caller(uint32 x) {
    requires x <= 1000u32;
    ensures result == x;
} by {
    step();
    step();
    step();
    step();
    step();
    step() {
        requires statement(3).call(first, 0).parameter(p).a <= 1000u32 by close();
    }
    have at(statement(3).call(first, 0).entry, statement(3).call(first, 0).parameter(p).a) == x;
    have at(statement(3).call(first, 0).entry, statement(3).call(first, 0).parameter(p).b) == 2u32;
}
```

```expect
pass
```
