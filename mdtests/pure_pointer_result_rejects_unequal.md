# Unfolding a pointer result does not identify unequal pointers

```click
function identity(p: int32*) -> int32* { p }
theorem unequal(p: int32*, q: int32*) {
    requires p != q;
    ensures identity(p) == q by { unfold(identity(p)); normalize(); }
}
```
```expect
fail: goal did not normalize to true
```
