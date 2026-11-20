# Reflexive algebraic comparisons survive lowering and rewriting

```click
spec enum Flag { Up, Down }

theorem written_equal() {
    ensures forall (unused: Integer) { Flag::Up == Flag::Up } by {
        intro();
        normalize();
    }
}

theorem rewritten_equal(f: Flag) {
    requires f == Flag::Up;
    ensures f == Flag::Up by {
        rewrite(f, Flag::Up);
        normalize();
    }
}

theorem written_not_equal() {
    ensures forall (unused: Integer) { not (Flag::Up != Flag::Up) } by {
        intro();
        normalize();
    }
}

theorem rewritten_not_equal(f: Flag) {
    requires f == Flag::Up;
    ensures not (f != Flag::Up) by {
        rewrite(f, Flag::Up);
        normalize();
    }
}
```

```expect
pass
```
