# A null assignment preserves the loop object-class join

Null designates no object. Accept it at the back edge without giving the
null value the head's object class.

```c filename=nullloop.c
struct node { int32 v; };
void f(struct node* p, int32 more) {
    while (more) { p = 0; more = more - 1; }
}
```
```click
verifying "nullloop.c";
void f(struct node* p, int32 more) {
    requires 0 <= more;
    ensures 1 == 1;
} by {
    loop {
        decreases more;
        invariant 0 <= more;
        initialize by simp();
        preserve by { step(); step(); close_invariants() by simp(); }
    }
    execute();
}
```

```expect
pass
```
