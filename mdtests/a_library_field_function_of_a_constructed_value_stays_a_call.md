# A library field function of a constructed value stays a call

A library function whose body is `match s { V(.., x, ..) => x }`, as
`slice::len` and `slice::as_ptr` are, lowers as the call that was written,
like any other function: `slice::len(Slice<uint8>::Slice(p, m))` is a call,
not `m`. `unfold` opens it to the constructor's field. The goal is therefore
the same term whether the constructed value is written at the call or
arrives by `rewrite`, and the same `unfold` opens it in both.

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
        known();
    }
}

theorem from_its_parts(p: uint8*, m: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, m)) == m by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        known();
    }
    ensures slice::as_ptr(Slice<uint8>::Slice(p, m)) == p by {
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, m)));
        known();
    }
}

theorem after_a_rewrite(s: Slice<uint8>, p: uint8*, n: uint64) {
    requires s == Slice<uint8>::Slice(p, n);
    ensures slice::len(s) == n by {
        rewrite(s, Slice<uint8>::Slice(p, n));
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        known();
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
