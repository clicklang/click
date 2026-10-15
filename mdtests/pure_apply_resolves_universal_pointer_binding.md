# Applying a theorem to a universally bound pointer

```click
theorem pointer_refl(p: int32*) { ensures p == p by { normalize(); } }
theorem quantified_pointer_refl() {
    ensures forall (p: int32*) { p == p } by {
        intro();
        apply(pointer_refl(p));
        assumption();
    }
}
```
```expect
pass
```
