# Pure match fields do not enter the following proof

```click
spec enum Item { Value(int32) }
theorem escape(item: Item) {
    ensures 1 == 1 by {
        match item { Item::Value(value) => { }, }
        have value == value by { normalize(); }
        normalize();
    }
}
```
```expect
fail: could not lower `have` proposition
```
