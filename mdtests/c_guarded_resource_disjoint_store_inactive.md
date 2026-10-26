```c filename=frame.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    return 0;
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
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left == 0;
    requires root->base.left != root as (void *) as (struct base *);
    ensures result == 0;
    ensures child.number == old(child.number);
} by { unfold(child); step_until(function.exit); fold(child); solve(); }
```
```expect
pass
```
