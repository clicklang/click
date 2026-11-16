# A library field function of a constructed value is the field

Library field accessors follow the same unfolding rule as locally defined
functions. State their defining equations explicitly; a constructor argument
alone does not unfold a call.

```click
import click::rust::slice;

spec enum Pair {
    Pair(uint64, uint64),
}

function second(p: Pair) -> uint64 {
    match p {
        Pair::Pair(_, b) => b,
    }
}

theorem a_program_function_stays_a_call(a: uint64) {
    ensures second(Pair::Pair(a, 7u64)) == 7u64 by {
        unfold(second(Pair::Pair(a, 7u64)));
        normalize();
    }
}

theorem from_its_parts(p: uint8*, m: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, m)) == m by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        normalize();
    }
    ensures slice::as_ptr(Slice<uint8>::Slice(p, m)) == p by {
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, m)));
        normalize();
    }
}

theorem an_opaque_slice(s: Slice<uint8>) {
    requires s == Slice<uint8>::Slice(0, 3u64);
    ensures slice::len(s) == 3u64 by {
        unfold(slice::len(s));
        solve();
    }
}
```

```expect
pass
```
