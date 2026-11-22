# Viewability restricts over arbitrary resource descriptors

```click
import click::separation;
abstract resource token(id: int32);

theorem restrict_view(A: Resource, B: Resource) {
    requires viewable(A);
    requires contains(A, B);
    ensures viewable(B) by {
        apply(separation::viewable_restrict(A, B));
    }
}

theorem view_component(A: Resource, B: Resource) {
    requires viewable(A * B);
    ensures viewable(B) by {
        have contains(A * B, B) by {
            apply(separation::contains_right(A, B));
        }
        apply(separation::viewable_restrict(A * B, B));
    }
}

theorem named_view(k: int32) {
    requires viewable(token(k) * token(0));
    ensures viewable(token(k)) by {
        have contains(token(k) * token(0), token(k)) by {
            apply(separation::contains_left(token(k), token(0)));
        }
        apply(separation::viewable_restrict(token(k) * token(0), token(k)));
    }
}
```

```expect
pass
```
