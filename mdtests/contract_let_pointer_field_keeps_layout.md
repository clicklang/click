# Contract-let field requirement

```c filename=contract_let_field.c
struct arena { int* data; };
struct region { struct arena* arena; };
void touch(struct region* region) {}
void caller(struct region* second) { touch(second); }
```

```click
verifying "contract_let_field.c";
void touch(struct region* region) {
    let saved: struct arena* = region->arena;
    owns *region;
    owns region->arena->data;
    requires separate(memory(*region), memory(saved->data));
}
void caller(struct region* second) {
    owns *second;
    owns second->arena->data;
} by {
    step() {
        requires separate(memory(*second), memory(second->arena->data)) by { close(); }
    }
}
```

```expect
pass
```
