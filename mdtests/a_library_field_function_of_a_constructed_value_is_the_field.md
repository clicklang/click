# Library field functions use their defining equations

Library field accessors follow the same unfolding rule as locally defined
functions. State their equations explicitly when applying an iterator axiom
to a slice built from its pointer and length: `unfold` exposes the field,
and the proof uses that equation to relate the axiom's conclusion to the
goal. A constructor argument alone does not unfold a call.

```click
import click::rust::slice;
import click::rust::chunks_exact;

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

theorem chunk_count(p: uint8*, m: uint64) {
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).len() == m / 4u64 by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        apply(chunks_exact::len_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
        solve();
    }
}

theorem chunk_at(p: uint8*, m: uint64, k: uint64) {
    requires k < m / 4u64;
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).nth(k).as_ptr() == p + k * 4u64 by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, m)));
        apply(chunks_exact::nth_chunks_exact(Slice<uint8>::Slice(p, m), 4u64, k));
        solve();
    }
}

theorem tail(p: uint8*, m: uint64) {
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).remainder().len() == m % 4u64 by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, m)));
        apply(chunks_exact::remainder_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
        solve();
    }
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).remainder().as_ptr() == p + (m - m % 4u64) by {
        unfold(slice::len(Slice<uint8>::Slice(p, m)));
        unfold(slice::as_ptr(Slice<uint8>::Slice(p, m)));
        apply(chunks_exact::remainder_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
        solve();
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
