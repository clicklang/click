# Slice iterator as a library value

`sum.rs` is a byte-for-byte copy of `examples/rust-iter-references/sum.rs`:
`for byte in bytes.iter()` summing the bytes it reads through each yielded
reference. The unit sets `"iterators": "library"`, so the iterator is one
value of the library's `SliceIter<uint8>` (`click::rust::slice_iter`,
`design/rust-iterators.md`) and no base, length or remaining-count local is
named.

`sum.click` proves the same contract as the example: the exact mathematical
sum of the input bytes for lengths `0..=1000`. The loop carries where the
iterator stands as an ordinary invariant,
`iter.as_slice().as_ptr() == bytes + (bytes.len() - iter.len())`. The
`next()` call's contract says the remaining slice starts one element later
and is one shorter; the proof carries the invariant across it with one
pointer-association theorem it states itself.

The native Charon artifact and import lock are committed for offline checks.
The nightly test `charon_slice_iter_sums_bytes_by_its_library_contract`
verifies the proof and rejects a missing view, a false result, a shifted
position invariant, a wrong step and a non-decreasing measure.

The base case is proved at the literal `0u64`: the proof first states
`bytes.len() - loop(0).iter.len() == 0u64` and rewrites with it. Stating it
at the iterator's own length also verifies, but its expansion does not
re-verify (`bugs/peel-rejects-a-listed-guard-after-a-have-proved-by-rewrite-and-normalize.md`).
The tools test `charon_slice_iter_tools_recheck_expanded_certificate`
expands and re-verifies the proof.
