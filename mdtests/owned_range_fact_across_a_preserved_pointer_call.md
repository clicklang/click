# An owned range fact across a call preserving its pointer

```c filename=frame.c
struct Box { int *p; int start; };
void touch(struct Box *box) {}
int read_saved(struct Box *box) {
    touch(box);
    return box->p[box->start];
}
```

```click
verifying "frame.c";
resource saved(p: int32*) {
    field value: int32;
    owns *p;
    fact *p == value;
}
resource region(box: struct Box*) {
    field start: int32;
    field end: int32;
    owns *box;
    owns box->p[start..end];
    fact box->start == start;
    fact 0 <= start;
    fact start < end;
}
void touch(struct Box *box) {
    owns *box;
    ensures box->p == old(box->p);
    ensures box->start == old(box->start);
}
int read_saved(struct Box *box) {
    owns r: region(box);
    requires aligned(box, 8);
    requires box->p[box->start] == 22;
    ensures result == 22;
} by {
    mark before;
    let { start: k, end: e } = unfold(r);
    let kept = fold(saved(box->p + k), { value: 22 });
    step();
    have box->p == at(before, box->p);
    unfold(kept);
    have box->start == k;
    have at(before, box->p)[k] == 22 by { assumption(); }
    have box->p + box->start == at(before, box->p) + k by {
        normalize() using { box->start == k; box->p == at(before, box->p); };
    }
    have box->p[box->start] == 22 by {
        transport(at(before, box->p)[k] == 22, box->p[box->start] == 22) using {
            at(before, box->p)[k] == 22;
            box->p + box->start == at(before, box->p) + k;
        };
    }
    let r = fold(region(box), { start: k, end: e });
    step();
}
```

```expect
pass
```
