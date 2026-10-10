# A stored pointer remains the child argument after an unfold

The C stores a loaded pointer through an alias returned by a helper, then
changes the source field. A resource tactic packages the destination cell and
its child; unfolding and refolding that package must retain the stored pointer.
Materializing the destination under another address spelling as an untyped
scalar placeholder used to hide that pointer and make the final fold fail.
```c filename=stored_pointer_child.c
struct node { struct node *next; };
struct node *same(struct node *p) { return p; }
void set(struct node *p, struct node *q, struct node *r) {
    struct node *alias = same(p);
    struct node *tmp = q->next;
    alias->next = tmp;
    q->next = r;
}
```
```click
verifying "stored_pointer_child.c";
struct node* same(struct node* p) { ensures result == p; } by { execute(); simp(); }
resource leaf(p: struct node*) {
    field tag: int32;
    owns p->next;
}
resource box(p: struct node*) {
    field tag: int32;
    owns p->next;
    owns child: leaf(p->next);
    fact child.tag == tag;
}
tactic pack(p: struct node*, q: struct node*) {
    consumes p->next;
    consumes child: leaf(q);
    requires p->next == q;
    produces whole: box(p);
    ensures whole.tag == old(child.tag);
} by {
    let whole = fold(box(p), { tag: child.tag }, { child: child });
    have whole.tag == old(child.tag);
}
void set(struct node* p, struct node* q, struct node* r) {
    consumes p->next;
    owns q->next;
    consumes child: leaf(q->next);
    produces whole: box(p);
    ensures whole.tag == old(child.tag);
} by {
    execute_until(statement(6));
    have p->next == tmp;
    let { whole: packaged } = pack(p, tmp, { child: child });
    let { child: returned } = unfold(packaged);
    let whole = fold(box(p), { tag: returned.tag }, { child: returned });
    step(); simp();
}
```
```expect
pass
```
