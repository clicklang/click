# A call's `.parameter(name)` names only a by-value struct parameter

`.parameter(name)` is the callee's copy of a by-value aggregate argument. A
name the callee does not take by value as a struct, here the scalar `x`, has
no copy, and the spelling is refused with what the call has.

```c filename=call_parameter_names.c
struct pair { uint32 a; uint32 b; };

uint32 first(struct pair p, uint32 x) {
    return p.a;
}

uint32 caller(uint32 x) {
    struct pair q;
    q.a = x;
    q.b = 2;
    return first(q, 1);
}
```

```click
verifying "call_parameter_names.c";

uint32 first(struct pair p, uint32 x) {
    requires p.a <= 1000u32;
    requires x <= 1000u32;
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
    have statement(3).call(first, 0).parameter(x).a == 1u32;
}
```

```expect
fail: has no by-value aggregate parameter `x`
```
