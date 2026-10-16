# Source expansion uses parsed name bindings

Comments may hold punctuation, apparent declarations and `#`. They do not
change selective imports or shadowing. A resource family and its instance
may share a name; a local theorem does not replace an explicitly qualified
library theorem.

```c filename=keep.c
void keep(int32* p) { }
```

```click
/* # ; theorem fake() {} */
import /* ; */ click::list::{append, append_left_identity};
verifying "keep.c";
resource cell(p: int32*) {
    field marker: int32;
    owns *p;
    fact marker == 0;
}

/* banner */ theorem int32_positive_is_nonnegative(x: int32) {
    ensures x == x by simp();
}

theorem client(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}

void keep(int32* p) {
    owns cell: cell(p);
} by {
    unfold(cell);
    execute();
    let cell = fold(cell(p), { marker: 0 });
    simp();
}
```

```expect
pass
```
