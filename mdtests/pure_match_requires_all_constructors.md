# Pure match requires the entire constructor family

```click
spec enum Item { Empty, Value(int32) }
theorem missing(item: Item) {
    ensures item == Item::Empty by {
        match item { Item::Empty => { assumption(); }, }
    }
}
```
```expect
fail: match must cover every constructor exactly once
```
