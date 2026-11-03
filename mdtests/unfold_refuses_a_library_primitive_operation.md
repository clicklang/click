# unfold refuses a library primitive operation

```click
import click::rust::vec;

theorem open_len(v: Vec<uint32>) {
    ensures vec::len(v) == vec::len(v) by {
        unfold(vec::len(v));
    }
}
```

```expect
fail: `unfold` cannot open `click::rust::vec::len`: it is a library primitive operation
```
