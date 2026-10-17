# Named-contract entry uses one meaning for an explicit pointer cast

The provisional resource and the checked entry clause must retain the same
pointer view after converting through `void*`. Treating the native fragment as
an implicit coercion while specification lowering applies an explicit cast
made setup reject its own resource argument.

```c filename=case.c
struct node { int value; };
void keep(struct node* p) {}
```
```click
verifying "case.c";
resource cell(p: struct node*) { field value: int32; owns p->value; }
contract void Keep(struct node* p) {
    owns held: cell((struct node*)(void*)p);
}
void keep(struct node* p) { ensures true; } by { execute(); }
```
```expect
pass
```
