# A by-value struct argument is spelled by its call's parameter

`first` takes `struct pair` by value. A call copies the argument into the
callee's parameter object, and the callee's contract reads that copy: the
requirement `p.a <= 1000u32` is about the copy, read at the memory just after
the copy was made. The caller has no local naming the copy, and no recorded
point holds that memory.

The call names the copy where it makes it: a call's region has, for each
by-value aggregate parameter, `.parameter(name)`, the callee's copy read at the
call. So the step that runs the call writes its requirement as
`statement(3).call(first, 0).parameter(p).a <= 1000u32`, which lowers to the
very obligation the call leaves open, and proves it from the caller's own
facts. After the call the copy keeps its name, here as `x`.

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
    step() {
        requires statement(3).call(first, 0).parameter(p).a <= 1000u32 by solve();
    }
    have statement(3).call(first, 0).parameter(p).a == x;
    have statement(3).call(first, 0).parameter(p).b == 2u32;
}
```

```expect
pass
```
