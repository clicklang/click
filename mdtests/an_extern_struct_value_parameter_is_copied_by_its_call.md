# An extern struct value parameter is copied by its call

`first` has only a prototype; its contract is the sidecar's `extern`
declaration. Its parameter is a `struct pair` taken by value, so a call copies
the argument into an object of the struct's layout and the contract reads that
copy. The `extern` declaration gives the parameter that layout, as a C
definition's parameter has, and the caller's step proves the requirement over
the copy.

```c filename=extern_struct_value.c
struct pair { uint32 a; uint32 b; };

uint32 first(struct pair p);

uint32 caller(uint32 x) {
    struct pair q;
    q.a = x;
    q.b = 2;
    return first(q);
}
```

```click
verifying "extern_struct_value.c";

extern uint32 first(struct pair p) {
    requires p.a <= 1000u32;
    ensures result == p.a;
}

uint32 caller(uint32 x) {
    requires x <= 1000u32;
    ensures result == x;
}
```

```expect
pass
```
