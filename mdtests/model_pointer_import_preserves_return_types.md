# An imported pointer return retains its declared nonnull type guarantee

```c filename=model_pointer_return_interface.c
struct node { unsigned long long word; };
struct node* get(struct node* p) { return p; }
int caller(struct node* p) {
    struct node* q = get(p);
    if (q != 0) return 1;
    return 0;
}
```

```click
verifying "model_pointer_return_interface.c";
import "model_pointer_return_interface.click";
int32 caller(struct node* p) {
    requires node_type(p) == 1;
    ensures result == 0 or result == 1;
} by {
    step(); step();
    if q != 0 {
        have node_type(q) == 1;
        execute(); simp();
    } else { execute(); simp(); }
}
```

```expect
pass
```
