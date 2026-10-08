# Theorem application retains proved constructor inequalities

Bare `apply` must cite a constructor inequality that `have` proved. The
planner can recognize it as context-free, but the explicit theorem checker
still requires that evidence; dropping it produces a rejected certificate.

```click
spec enum Tree { Empty, Node(int32), }

theorem nonempty(child: Tree) {
    requires not(child == Tree::Empty);
    ensures not(child == Tree::Empty) by { assumption(); }
}

theorem concrete(child: int32) {
    ensures not(Tree::Node(child) == Tree::Empty) by {
        have not(Tree::Node(child) == Tree::Empty) by { normalize(); }
        apply(nonempty(Tree::Node(child)));
        assumption();
    }
}

theorem concrete_explicit(child: int32) {
    ensures not(Tree::Node(child) == Tree::Empty) by {
        have not(Tree::Node(child) == Tree::Empty) by { normalize(); }
        apply(nonempty(Tree::Node(child))) using {
            not(Tree::Node(child) == Tree::Empty);
        }
        assumption();
    }
}
```

```expect
pass
```
