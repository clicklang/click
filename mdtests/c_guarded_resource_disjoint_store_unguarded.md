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
    owns ((struct cell*)(void*)p)->value;
    fact ((struct cell*)(void*)p)->value == number;
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != (struct base*)(void*)root;
    ensures result == old(child.number);
    ensures child.number == old(child.number);
    ensures root->value == old(child.number);
} by { unfold(child); execute(); fold(child); simp(); }
```
```expect
pass
```
