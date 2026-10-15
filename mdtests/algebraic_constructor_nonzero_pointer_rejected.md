# Nonzero integers remain invalid in pointer-valued constructor fields

The constructor null-pointer rule accepts only literal `0`. A nonzero integer
cannot inhabit a C pointer field, including in an ordinary contract.

```c filename=constructor_null.c
void keep(int32 *p) {}
void generic_keep(int32 *p) {}
```

```click
verifying "constructor_null.c";

spec enum PointerPair { Pair(int32*, int32*) }

function identity<T>(value: T) -> T { value }

resource pair_at(p: int32*) {
    field model: PointerPair;
}

void keep(int32* p) {
    owns state: pair_at(p);
    requires state.model == PointerPair::Pair(p, 1);
    ensures state.model == PointerPair::Pair(p, 1);
} by {
    execute(); simp();
}

void generic_keep(int32* p) {
    owns state: pair_at(p);
    requires state.model == identity(PointerPair::Pair(p, 1));
    ensures state.model == identity(PointerPair::Pair(p, 1));
} by {
    execute(); simp();
}
```

```expect
fail: constructor `PointerPair::Pair` argument 1 expects int32*, got int32
```
