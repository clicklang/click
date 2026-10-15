# Null constants in pointer-valued constructor fields

An ordinary function contract may construct an algebraic value whose C pointer
field is null. The constructor uses the field's pointer type for the literal
`0`, just as a pure function or resource argument does.

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
    requires state.model == PointerPair::Pair(p, 0);
    ensures state.model == PointerPair::Pair(p, 0);
} by {
    execute(); simp();
}

void generic_keep(int32* p) {
    owns state: pair_at(p);
    requires state.model == identity(PointerPair::Pair(p, 0));
    ensures state.model == identity(PointerPair::Pair(p, 0));
} by {
    execute(); simp();
}
```

```expect
pass
```
