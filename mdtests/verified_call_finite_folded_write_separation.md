# A call proves separation for finite nested ownership

The calls write a left field held by a nested resource. An ordinary
wrapper and a named child both contribute the checked left-field range.
The right-field view stays live across each call.

```c filename=verified_call_finite_folded_write_separation.c
struct pair {
    int left;
    int right;
};

void write_wrapped(struct pair *p);
void write_named(struct pair *p);
void write_selected(struct pair *p);

int read_beside_wrapped(struct pair *p) {
    write_wrapped(p);
    return p->right;
}

int read_beside_named(struct pair *p) {
    write_named(p);
    return p->right;
}

int read_beside_selected(struct pair *p) {
    write_selected(p);
    return p->right;
}
```

```click
resource left_cell(p: struct pair*) {
    owns p->left;
}

resource wrapped(p: struct pair*) {
    owns left_cell(p);
}

resource tagged_left(p: struct pair*) {
    field tag: int32;
    owns p->left;
}

resource named_wrapper(p: struct pair*) {
    field tag: int32;
    owns child: tagged_left(p);
    fact child.tag == tag;
}

spec enum Selection {
    Left,
    Right,
}

resource selected(p: struct pair*) {
    field choice: Selection;
    match choice {
        Selection::Left => { owns p->left; },
        Selection::Right => { owns p->right; },
    }
}

verifying "verified_call_finite_folded_write_separation.c";

extern void write_wrapped(struct pair* p) {
    owns wrapped(p);
}

extern void write_named(struct pair* p) {
    owns r: named_wrapper(p);
}

extern void write_selected(struct pair* p) {
    owns r: selected(p);
}

int32 read_beside_wrapped(struct pair* p) {
    owns wrapped(p);
    views p->right;
    requires separate(memory(p->left), memory(p->right));
    ensures result == old(p->right);
} by {
    step() by { known(); }
}

int32 read_beside_named(struct pair* p) {
    owns r: named_wrapper(p);
    views p->right;
    requires separate(memory(p->left), memory(p->right));
    ensures result == old(p->right);
} by {
    step(write_named, { r: r }) by { known(); }
}

int32 read_beside_selected(struct pair* p) {
    owns r: selected(p);
    requires r.choice == Selection::Left;
    views p->right;
    requires separate(memory(p->left), memory(p->right));
    ensures result == old(p->right);
} by {
    step(write_selected, { r: r }) by { known(); }
}
```

```expect
pass
```
