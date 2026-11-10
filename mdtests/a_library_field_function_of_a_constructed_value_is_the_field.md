# A library field function of a constructed value is the field

A library function whose body is `match s { V(.., x, ..) => x }` is one
field of its argument, as `slice::len` and `slice::as_ptr` are. Applied to a
value built with that constructor it is the field, by its definition,
wherever the value arrives: written at the call, or bound to a theorem's
parameter by `apply`. So an axiom stated over a slice applies to a slice
built from its data pointer and its length, the form a slice has in a proof
about a program, with nothing unfolded. Applied to any other value the
function stays as written, and `unfold` opens it as before. A program's own
function always stays the call that was written: `second` below is opened
with `unfold`.

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
        apply(chunks_exact::len_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
    }
}

theorem chunk_at(p: uint8*, m: uint64, k: uint64) {
    requires k < m / 4u64;
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).nth(k).as_ptr() == p + k * 4u64 by {
        apply(chunks_exact::nth_chunks_exact(Slice<uint8>::Slice(p, m), 4u64, k));
    }
}

theorem tail(p: uint8*, m: uint64) {
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).remainder().len() == m % 4u64 by {
        apply(chunks_exact::remainder_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
    }
    ensures Slice<uint8>::Slice(p, m).chunks_exact(4u64).remainder().as_ptr() == p + (m - m % 4u64) by {
        apply(chunks_exact::remainder_chunks_exact(Slice<uint8>::Slice(p, m), 4u64));
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
