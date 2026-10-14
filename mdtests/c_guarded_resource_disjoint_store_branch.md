```c filename=frame.c
struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    int32 result = 0;
    if (root->base.left) {
        struct base* child = root->base.left;
        int32 value = ((struct cell*)(void*)child)->value;
        root->value = value;
        result = value;
    }
    return result;
}
```
```click
verifying "frame.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns ((struct cell*)(void*)p)->value;
        fact ((struct cell*)(void*)p)->value == number;
    }
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != (struct base*)(void*)root;
    ensures root->base.left != 0 implies result == old(child.number);
    ensures child.number == old(child.number);
    ensures root->base.left != 0 implies root->value == old(child.number);
} by {
    if root->base.left != 0 {
        unfold(child); execute(); fold(child); simp();
    } else {
        unfold(child); execute(); fold(child); simp();
    }
}
```
```expect
pass
```
