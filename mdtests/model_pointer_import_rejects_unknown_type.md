# Importing a contract does not drop its declared object-type requirement

```c filename=model_pointer_import_interface.c
struct model_node { unsigned long long word; };
void imported_node(struct model_node* p) {}
void typed_caller(struct model_node* p) { imported_node(p); }
void untyped_caller(void* p) { imported_node((struct model_node*)p); }
```

```click
import "model_pointer_import_interface.click";
verifying "model_pointer_import_interface.c";
void untyped_caller(void* p) {
    produces held: imported_node_token();
    ensures true;
} by {
    let { held: held } = step(imported_node((struct model_node*)p), {});
    execute();
}
```

```expect
fail: requires original object class `struct model_node` or null
```
