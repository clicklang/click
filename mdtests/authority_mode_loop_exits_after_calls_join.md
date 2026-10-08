# Loop exits after calls join in authority mode

Each exit reaches the join through a different call, so its creation ledger
is a different successor. Neither ledger records any storage, member or
authority event, so the exits still have a common successor.

```c filename=paint_through_helper.c
struct node { int32 shade; };

static void repaint(struct node* p) {
    int32 next = 0;
    p->shade = next;
}

void paint(struct node* p, int32 flag) {
    while (true) {
        if (flag == 0) {
            repaint(p);
            break;
        } else {
            p->shade = 0;
            break;
        }
    }
}
```

```click
verifying "paint_through_helper.c";

void paint(struct node* p, int32 flag) {
    owns p->shade;
    ensures p->shade == 0;
} by {
    loop {
        decreases 0;
        owns p->shade;

        preserve by {
            if flag == 0 {
                step();
                step();
                step();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
