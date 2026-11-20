# Naming a read from a multi-field store

The copy records both field stores at its exit. A later store to the right
field leaves the left field's version available at the same point.

```c filename=copy.c
struct Pair { int32 left; int32 right; };

int32 copy_left(int32 left, int32 right) {
    struct Pair source;
    struct Pair target;
    source.left = left;
    source.right = right;
    target = source;
    target.right = 9;
    return target.left;
}
```

```click
verifying "copy.c";
int32 copy_left(int32 left, int32 right) {
    ensures result == left;
} by {
    step_until(statement(5).entry);
    mark copied;
    have target.left == left;
    have target.right == right;
    step();
    have target.left == at(copied, target.left);
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
