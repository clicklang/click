# A chunks_exact iterator reads with its library contract

`click::rust::chunks_exact` describes Rust's `ChunksExact<T>` by a contract,
not by verifier code (`design/rust-iterators.md`): an iterator value is the
chunks it will still yield, `it.len()` of them, the `k`-th `it.nth(k)`. The
axioms say what `s.chunks_exact(n)` builds and what one `next()` leaves, and
a proof cites them. Chunk `k` starts at element `k * 4`, at a symbolic `k`.

```click
import click::rust::slice;
import click::rust::chunks_exact;

theorem chunk_count(s: Slice<uint8>) {
    ensures s.chunks_exact(4u64).len() == s.len() / 4u64 by {
        apply(chunks_exact::len_chunks_exact(s, 4u64));
    }
}

theorem chunk_at(s: Slice<uint8>, k: uint64) {
    requires k < s.len() / 4u64;
    ensures s.chunks_exact(4u64).nth(k).as_ptr() == s.as_ptr() + k * 4u64 by {
        apply(chunks_exact::nth_chunks_exact(s, 4u64, k));
    }
    ensures s.chunks_exact(4u64).nth(k).len() == 4u64 by {
        apply(chunks_exact::nth_chunks_exact(s, 4u64, k));
    }
}

theorem second_after_next(it: ChunksExact<uint8>) {
    requires 2u64 <= it.len();
    ensures it.after_next().nth(0u64) == it.nth(1u64) by {
        have 0u64 < it.len();
        have 0u64 < it.len() - 1u64;
        apply(chunks_exact::nth_after_next(it, 0u64));
    }
    ensures it.after_next().remainder() == it.remainder() by {
        have 0u64 < it.len();
        apply(chunks_exact::remainder_after_next(it));
    }
}
```

```expect
pass
```
