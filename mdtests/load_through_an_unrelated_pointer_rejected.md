# A read through an unrelated pointer does not see a store

The negative of `load_through_a_pointer_alias_after_a_store.md`. The frame
owns two cells, one named by `id`, which the C code reaches as `p`, and one
named by `other`, which no fact relates to `p`. The store through `p` says
nothing about `other->word`, so a claim that it reads the stored value is
refused. A read looks a cell up at another spelling only when the path
proves the two pointers equal.

```c filename=unrelated_loaded.c
struct node { unsigned long word; struct node *up; };

void set_up_word(struct node *c) {
    struct node *p;
    p = c->up;
    p->word = 5;
}
```

```click
verifying "unrelated_loaded.c";

spec enum Frame { Up(struct node*, struct node*, int) }

resource frame_at(c: struct node*) {
    field model: Frame;
    match model {
        Frame::Up(id, other, value) => {
            owns c->up;
            owns id->word;
            owns other->word;
            fact id != 0;
            fact other != 0;
            fact c->up == id;
            fact id->word == value;
            fact other->word == value;
        },
    }
}

void set_up_word(struct node* c) {
    consumes f: frame_at(c);
    requires 1 == 1;
} by {
    match f.model {
        Frame::Up(id, other, value) => {
            unfold(f);
            step();
            step();
            step();
            have other->word == 5;
            execute();
            simp();
        },
    }
}
```

```expect
fail: could not establish `other->word == 5`
```
