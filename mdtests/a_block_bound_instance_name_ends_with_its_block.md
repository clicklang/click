# A block-bound instance name ends with its block

An instance name bound inside a proof block, here by `unfold` in each arm of
an `if`, names its instance only to the end of that block, like every other
proof binder. The resource itself stays in the proof state; only the name ends.
Naming it after the block is refused by name. Bind it before the block, as in
`an_instance_bound_before_a_block_is_named_inside_it.md`, or name it in the
contract.

```c filename=a_block_bound_instance_name_ends_with_its_block.c
void f(int *q) {}
```

```click
verifying "a_block_bound_instance_name_ends_with_its_block.c";

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
    if b.v == 3 {
        let { k: kk } = unfold(b);
    } else {
        let { k: kk } = unfold(b);
    }
    let b = fold(box(q), { v: 3 }, { k: kk });
    execute();
}
```

```expect
fail: the resource instance `kk` is out of scope here: a name bound inside a block names its instance only to the end of that block; bind it before the block, or name it in the contract
```
