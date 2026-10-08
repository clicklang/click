# Pure pointer projection remains usable by resource folding
```c filename=box.c
struct Box { int value; struct Box *next; };
void round_trip(struct Box *p, int n) { while (n > 0) { p = p; n--; } }
```
```click
verifying "box.c";
spec enum Shape { Node(struct Box*), }
function select(s: Shape) -> struct Box* {
    match s { Shape::Node(p) => p, }
}
resource box(p: struct Box*) {
    field model: Shape;
    match model {
        Shape::Node(identity) => {
            owns p->value;
            owns p->next;
            fact p != 0;
            fact p == identity;
        },
    }
}
resource frame(child: struct Box*) {
    field model: Shape;
    match model {
        Shape::Node(identity) => {
            owns identity->value;
            owns identity->next;
            fact identity != 0;
            fact identity->next == child;
        },
    }
}
void round_trip(struct Box* p, int32 n) {
    consumes b: box(p);
    requires n >= 0;
    ensures 1 == 1;
} by {
    loop {
        owns b: box(p);
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
            match b.model {
                Shape::Node(identity) => {
                    unfold(b);
                    have select(Shape::Node(identity)) == identity by {
                        unfold(select(Shape::Node(identity))); normalize();
                    }
                    let f = fold(frame(p->next), { model: Shape::Node(identity) });
                    unfold(f);
                    let b = fold(box(p), { model: Shape::Node(identity) });
                    step(); step();
                    close_invariants();
                },
            }
        }
    }
    execute(); simp();
}
```
```expect
pass
```
