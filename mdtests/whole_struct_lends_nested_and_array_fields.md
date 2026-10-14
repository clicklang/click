# A whole struct lends its nested struct and array fields

`owns *p` is the complete storage of the struct `p` points at, including an
embedded struct and an inline array. A function holding it lends a callee
any of those fields by name, gets them back, and keeps the field the callee
did not own: `p->a` needs no frame in `set_inner`'s contract.

```c filename=whole_struct_lends_nested_and_array_fields.c
struct inner { int x; char c; };
struct outer { int a; struct inner in; int arr[3]; };

int set_inner(struct outer *p, int v) {
    p->in.x = v;
    p->arr[1] = v;
    return 0;
}

int caller(struct outer *p) {
    set_inner(p, 5);
    return p->a + p->in.x;
}
```

```click
verifying "whole_struct_lends_nested_and_array_fields.c";

int32 set_inner(struct outer* p, int32 v) {
    owns p->in;
    owns p->arr;
    ensures p->in.x == v;
    ensures p->arr[1] == v;
    ensures result == 0;
}

int32 caller(struct outer* p) {
    requires p->a == 1;
    owns *p;
    ensures p->a == 1;
    ensures p->arr[1] == 5;
    ensures result == 6;
}
```

```expect
pass
```
