# Known Integer counts follow model equality

Equality substitution passes through a C-valued getter, its mathematical
Integer observation, and Integer addition without an explicit rewrite.

```click
spec enum CountModel { Empty, Node(int32) }
function cached(tree: CountModel) -> int32 {
    match tree {
        CountModel::Empty => 0,
        CountModel::Node(value) => value,
    }
}
theorem transport_count(left: CountModel, right: CountModel, total: int32) {
    requires left == right;
    requires to_integer(total) == 1 + to_integer(cached(left));
    ensures to_integer(total) == 1 + to_integer(cached(right)) by {
        assumption();
    }
}

theorem transport_mask(left: uint32, right: uint32, mask: uint32) {
    requires left == right;
    ensures to_integer((left * mask) & mask) ==
            to_integer((right * mask) & mask) by {
        assumption();
    }
}
```

```expect
pass
```
