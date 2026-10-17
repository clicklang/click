# Imports retain nominal requirements from their declared contracts

The imported helper is also verified as its own entry module by the gate.

```c filename=model_pointer_import_interface.c
struct model_node { unsigned long long word; };
void imported_node(struct model_node* p) {}
void typed_caller(struct model_node* p) { imported_node(p); }
void untyped_caller(void* p) { imported_node((struct model_node*)p); }
```

```click
import "model_pointer_import_interface.click";
verifying "model_pointer_import_interface.c";
void typed_caller(struct model_node* p) {
    produces held: imported_node_token();
    ensures held.model == ImportedNodeRef::At(p);
} by {
    let { held: held } = step(imported_node(p), {});
    execute();
}
```

```expect
pass
```
