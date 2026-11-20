# A call reuses separation stated for the same byte spans

The two views compose into a known-bounds loan. The written separation uses
an opaque-bounds range over the same object and bytes.

```c filename=resize_links.c
struct links { struct links *left; struct links *right; };
struct node { struct links links; int size; };
extern void resize(struct links *p);
void invoke(struct links *p) { resize(p); }
```

```click
verifying "resize_links.c";

resource metadata(p: struct links*) {
    field value: int32;
    owns (p as (void *) as (struct node *))->size;
    fact (p as (void *) as (struct node *))->size == value;
}

extern void resize(struct links* p) {
    views (p as (void *) as (struct node *))->links.left;
    views (p as (void *) as (struct node *))->links.right;
    owns m: metadata(p);
    ensures m.value == 1;
}

void invoke(struct links* p) {
    views (p as (void *) as (struct node *))->links.left;
    views (p as (void *) as (struct node *))->links.right;
    owns m: metadata(p);
    ensures m.value == 1;
} by {
    have separate(memory((p as (void *) as (struct node *))->size), memory(*p)) by normalize();
    step(resize, { m: m });
}
```

```expect
pass
```
