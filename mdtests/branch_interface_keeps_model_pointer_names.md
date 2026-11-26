# A branch interface retains its model-bound pointer spelling

The interface exports a packed word using the outer model binding `id`.
A later state rewrite cancels the extra word. Verification used to pass,
but expansion printed an internal pointer as `…` instead of retaining `id`.

```c filename=probe.c
struct Node { unsigned long tag; struct Node *next; int32 other; };
void set_word(struct Node *q, struct Node *r, unsigned long stamp) {
    q->tag = (unsigned long)r + stamp;
}
void put(struct Node *p, struct Node *q, int32 x, unsigned long stamp) {
    struct Node *child = p->next;
    struct Node *r = q->next;
    set_word(child, r, stamp);
    if (x <= 0) { q->other = 0; } else { q->other = 1; }
}
```

```click
verifying "probe.c";
spec enum Model { At(struct Node*) }
resource identity(p: struct Node*) {
    field model: Model;
    match model { Model::At(id) => { owns p->other; fact p == id; }, }
}
void set_word(struct Node* q, struct Node* r, uint64 stamp) {
    owns q->tag;
    ensures q->tag == address(r) + stamp;
} by { step_until(function.exit); close(); }
theorem same_tag(base: uint64*, alias: uint64*) {
    requires base == alias;
    requires viewable(memory(*base));
    ensures *alias == *base by {
        rewrite(alias, base);
        close();
    }
}
void put(struct Node *p, struct Node *q, int32 x, uint64 stamp) {
    owns p->next;
    requires p->next == q;
    owns q->tag;
    owns q->other;
    owns q->next;
    consumes s: identity(q->next);
    ensures 1 == 1;
} by {
    match s.model { Model::At(id) => {
        unfold(s);
        step(); step(); step(); step();
        step(set_word);
        have child == q;
        have child->tag == address(id) + stamp by { rewrite(id, r); close(); }
        have viewable(memory(q->tag)) by { observe(q->tag); }
        have &child->tag == &q->tag by { rewrite(child, q); close(); }
        apply(same_tag(&q->tag, &child->tag));
        have q->tag == address(id) + stamp;
        branch ensuring { fact child->tag == address(id) + stamp; } {
            true => {
                step();
                have viewable(memory(q->tag)) by { observe(q->tag); }
                have &child->tag == &q->tag by { rewrite(child, q); close(); }
                apply(same_tag(&q->tag, &child->tag));
                have q->tag == address(id) + stamp;
                have child->tag == address(id) + stamp by {
                    rewrite(child->tag, q->tag);
                    close();
                }
            }
            false => {
                step();
                have viewable(memory(q->tag)) by { observe(q->tag); }
                have &child->tag == &q->tag by { rewrite(child, q); close(); }
                apply(same_tag(&q->tag, &child->tag));
                have q->tag == address(id) + stamp;
                have child->tag == address(id) + stamp by {
                    rewrite(child->tag, q->tag);
                    close();
                }
            }
        }
        mark joined;
        have at(joined, child->tag) - stamp == address(id) by {
            rewrite(at(joined, child->tag), address(id) + stamp);
            normalize() using {};
        }
        step_until(function.exit); close();
    }, }
}
```

```expect
pass
```
