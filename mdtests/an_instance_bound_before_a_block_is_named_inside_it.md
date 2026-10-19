# An instance bound before a block is named inside and after it

The instance `kk` is bound by an `unfold` before the proof `if`, so both arms
read it and the fold after the `if` consumes it. Compare
`a_block_bound_instance_name_ends_with_its_block.md`, which binds it inside
the arms.

```c filename=an_instance_bound_before_a_block_is_named_inside_it.c
void f(int *q) {}
```

```click
verifying "an_instance_bound_before_a_block_is_named_inside_it.c";

resource cell(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource box(q: int32*) {
    field v: int32;
    owns k: cell(q);
    fact k.v == v;
}

void f(int32* q) {
    owns b: box(q);
    requires b.v == 3;
} by {
    let { k: kk } = unfold(b);
    if kk.v == 3 {
        have kk.v == 3;
    } else {
        have kk.v == 3;
    }
    let b = fold(box(q), { v: 3 }, { k: kk });
    execute();
}
```

```expect
pass
```
