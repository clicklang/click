# A C result parameter keeps its field binding

```c filename=select.c
struct object { int32 value; };
struct object* select(struct object* result, struct object* next) {
    return next;
}
```

```click
verifying "select.c";
struct object* select(struct object* result, struct object* next) {
    views result->value;
    views next->value;
    requires c(result)->value == 3 and next->value == 7;
    ensures c(result)->value == 3 and result->value == 7 by auto;
}
```

```expect
pass
```
