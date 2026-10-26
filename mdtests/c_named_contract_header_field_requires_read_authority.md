```c filename=frame.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    return value;
}
```
```click
verifying "frame.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns (p as (void *) as (struct cell *))->value;
        fact (p as (void *) as (struct cell *))->value == number;
    }
}
contract int32 Linked(struct cell* root) {
    requires root != 0;
    owns child: child_value(root->base.left);
}
```
```expect
fail: required access authority is unavailable
```
