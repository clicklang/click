# Pointer-valued pure functions preserve their declared sort

Opaque pointer applications retain their arguments until checked unfolding.
Null, recursive selectors, nested applications, and equality rewriting must
all work without converting a pointer result to an integer address.

```click
function identity(p: int32*) -> int32* { p }
function holds(p: int32*) -> int32 { 1 }
theorem use_identity(p: int32*) {
    ensures holds(identity(p)) == 1 by { unfold(holds(identity(p))); normalize(); }
    ensures identity(p) == p by { unfold(identity(p)); normalize(); }
}
spec enum Link { Empty, Node(int32*, Link), }
function last(link: Link) -> int32* decreases link {
    match link {
        Link::Empty => 0,
        Link::Node(p, tail) => match tail {
            Link::Empty => p,
            Link::Node(q, rest) => last(tail),
        },
    }
}
theorem selector(p: int32*, q: int32*) {
    ensures last(Link::Empty) == 0 by { unfold(last(Link::Empty)); normalize(); }
    ensures last(Link::Node(p, Link::Empty)) == p by {
        unfold(last(Link::Node(p, Link::Empty))); normalize();
    }
    ensures last(Link::Node(p, Link::Node(q, Link::Empty))) == q by {
        unfold(last(Link::Node(p, Link::Node(q, Link::Empty))));
        unfold(last(Link::Node(q, Link::Empty))); normalize();
    }
}
theorem nested(p: int32*, q: int32*) {
    requires p == q;
    ensures identity(p) == identity(q) by { rewrite(p == q); normalize(); }
    ensures identity(identity(p)) == p by {
        unfold(identity(identity(p))); unfold(identity(p)); normalize();
    }
    ensures holds(identity(p)) == holds(p) by {
        unfold(identity(p)); normalize();
    }
}
theorem rewrite_application(p: int32*, q: int32*) {
    requires identity(p) == q;
    ensures holds(identity(p)) == holds(q) by {
        rewrite(identity(p) == q); normalize();
    }
}
theorem applied_identity(p: int32*) {
    ensures identity(p) == p by { apply(use_identity(p)); assumption(); }
}
theorem opaque_assumption(p: int32*, q: int32*) {
    requires identity(p) == q;
    ensures identity(p) == q by simp;
}
```

```expect
pass
```
