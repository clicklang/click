# One changing arm blocks preservation of an uncached read

The other arm is disjoint, but the else arm overwrites the tag.

```c filename=join_rejects_changed_uncached_read.c
struct pair { uint64 tag; int32 count; int32 left; };
void touch(struct pair *p) { p->tag = 42; p->count = 17; }
void keep(struct pair *p, int32 x) {
    touch(p);
    if (x <= 0) { p->left = 0; } else { p->tag = 13; }
}
```

```click
verifying "join_rejects_changed_uncached_read.c";
void touch(struct pair* p) {
    requires p != 0;
    owns p->tag;
    owns p->count;
    ensures p->tag == 42;
    ensures p->count == 17;
} by { execute(); simp(); }
void keep(struct pair* p, int32 x) {
    requires p != 0;
    owns p->tag;
    owns p->count;
    owns p->left;
} by {
    step();
    have p->tag == 42 by { assumption(); }
    have p->count == 17 by { assumption(); }
    mark before_join;
    branch ensuring { fact 1 == 1; } then { step(); } else { step(); }
    have p->tag == 42 by { assumption(); }
    have p->count == 17 by { assumption(); }
    step();
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
