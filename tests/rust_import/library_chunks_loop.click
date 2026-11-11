import click::rust::slice;
import click::rust::chunks_exact;
import click::integer;
verifying "borrow.rs";

fn cover(bytes: &[u8]) -> usize {
    views bytes[0..bytes.len()];
    ensures result == bytes.len() % 4u64;
    ensures forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    };
} by {
    step_until(loop(0));
    have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64);
    have tail_len == bytes.len() % 4u64 by {
        apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
        solve();
    }
    have loop(0).iter.len() == bytes.len() / 4u64 by {
        apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
        solve();
    }
    loop {
        decreases iter.len();
        views bytes[0..bytes.len()];
        invariant tail_len == bytes.len() % 4u64;
        invariant iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations);
        invariant to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64);
        initialize by {
            have tail_len == bytes.len() % 4u64;
            have iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations) by {
                apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64)));
                have iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64);
                solve();
            }
            have to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64);
        }
        preserve by {
            step(); step(); step(); step();
            if 0u64 < iter.len() {
                have chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).len() == bytes.len() / 4u64 by {
                    apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
                }
                have iter.len() <= bytes.len() / 4u64;
                have to_integer((bytes.len() / 4u64 - iter.len())) == iterations;
                have (bytes.len() / 4u64 - iter.len()) < chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).len();
                have iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64).nth((bytes.len() / 4u64 - iter.len())) by {
                    apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations, 0u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.nth(0u64).len() == 4u64 by {
                    apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.nth(0u64).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len()) * 4u64 by {
                    apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, (bytes.len() / 4u64 - iter.len())));
                    solve();
                }
                have iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations + 1) by {
                    apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations));
                    solve();
                }
                have iter.after_next().len() == iter.len() - 1u64 by {
                    apply(chunks_exact::len_after_next(iter));
                }
                have (bytes.len() / 4u64 - iter.len()) <= 4611686018427387903u64;
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64) == to_integer((bytes.len() / 4u64 - iter.len())) * 4;
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64) < to_integer(bytes.len());
                have to_integer((bytes.len() / 4u64 - iter.len()) * 4u64 + 3u64) < to_integer(bytes.len());
                mark taken;
                step_until(read(0));
                have chunk == bytes + (bytes.len() / 4u64 - at(taken, iter.len())) * 4u64;
                have chunk_len == 4u64;
                step_until(loop(0).back_edge());
                have iter == at(taken, iter.after_next());
                have iter.len() == at(taken, iter.len()) - 1u64;
                have 0u64 < at(taken, iter.len());
                have iter.len() < at(taken, iter.len());
            } else {
                step();
            }
        }
    }
    have loop(0).iter.len() == 0u64;
    step_until(function.exit);
    have forall (k: usize) {
        k < bytes.len() implies bytes[k] == old(bytes[k])
    } by { intro(); intro(); solve(); }
    solve();
}
