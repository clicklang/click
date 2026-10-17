# `auto` opens a folded resource to store through it

`bump` stores to `p->value`, which `flat(p)` holds folded. The proof is
omitted, so `auto` executes the function. The store is refused while
`flat(p)` is folded; `auto` unfolds that one resource, whose body holds
`p->value`, and retries the store. At exit the contract's resource transition
folds `flat(p)` again. `click expand` writes the opening out as
`unfold(flat(p));`, so the expanded proof is the simple script a person would
write (design/proof-reuse.md, R4). A written `step()` never opens a resource
([`a_written_step_does_not_open_a_folded_resource.md`](a_written_step_does_not_open_a_folded_resource.md)).

```c filename=auto_opens_a_folded_resource_to_store_through_it.c
struct cell {
    int32 value;
    int32 other;
};

void bump(struct cell* p) {
    int32 seen = p->other;
    p->value = seen;
}
```

```click
resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "auto_opens_a_folded_resource_to_store_through_it.c";

void bump(struct cell* p) {
    owns flat(p);
}
```

```expect
pass
```
