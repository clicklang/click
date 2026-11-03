# library vec axioms reject an out-of-range read

`vec::get_push_kept` relates the values below the old length only; past it,
`vec::get` names a value the axioms say nothing about.

```click
import click::rust::vec;

theorem read_past_the_end(v: Vec<uint32>, x: uint32, i: uint64) {
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i) by {
        apply(vec::get_push_kept(v, x, i));
    }
}
```

```expect
fail: read_past_the_end.ensures_0
```
