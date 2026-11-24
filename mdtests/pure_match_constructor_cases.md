# Case analysis inside a pure theorem

```click
spec enum Item { Empty, Value(int32) }
function rebuild(item: Item) -> Item {
    match item {
        Item::Empty => Item::Empty,
        Item::Value(value) => Item::Value(value),
    }
}
theorem rebuild_is_identity(item: Item) {
    ensures rebuild(item) == item by {
        match item {
            Item::Empty => { rewrite(item, Item::Empty); unfold(rebuild(Item::Empty)); close(); },
            Item::Value(value) => { rewrite(item, Item::Value(value)); unfold(rebuild(Item::Value(value))); close(); },
        }
    }
}
theorem scoped_continuation(item: Item, outer_value: int32) {
    ensures outer_value == outer_value by {
        match item { Item::Empty => { }, Item::Value(value) => { }, }
        close();
    }
}
```
```expect
pass
```
