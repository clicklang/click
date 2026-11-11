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
        invariant iter.len() <= bytes.len() / 4u64;
        invariant forall (j: usize) {
            j < iter.len() implies
                iter.nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len() + j) * 4u64
        };
        invariant forall (j: usize) { j < iter.len() implies iter.nth(j).len() == 4u64 };
        initialize by {
            have tail_len == bytes.len() % 4u64;
            have iter.len() <= bytes.len() / 4u64;
            have forall (j: usize) {
                j < iter.len() implies
                    iter.nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len() + j) * 4u64
            } by {
                intro(); intro();
                have j < bytes.len() / 4u64;
                apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, j));
                solve();
            }
            have forall (j: usize) { j < iter.len() implies iter.nth(j).len() == 4u64 } by {
                intro(); intro();
                have j < bytes.len() / 4u64;
                apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64, j));
                solve();
            }
        }
        preserve by {
            step();
            step();
            step();
            step();
            if 0u64 < iter.len() {
                have iter.nth(0u64).len() == 4u64 by {
                    instantiate(forall (j: usize) { j < iter.len() implies iter.nth(j).len() == 4u64 }, 0u64);
                    solve();
                }
                have iter.nth(0u64).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len()) * 4u64 by {
                    instantiate(forall (j: usize) { j < iter.len() implies iter.nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len() + j) * 4u64 }, 0u64);
                    solve();
                }
                have iter.after_next().len() == iter.len() - 1u64 by {
                    apply(chunks_exact::len_after_next(iter));
                }
                have forall (j: usize) { j < iter.after_next().len() implies iter.after_next().nth(j).len() == 4u64 } by {
                    intro(); intro();
                    have j < iter.len() - 1u64;
                    apply(chunks_exact::nth_after_next(iter, j));
                    have j + 1u64 < iter.len();
                    have j + 1u64 <= 18446744073709551615u64;
                    instantiate(forall (j: usize) { j < iter.len() implies iter.nth(j).len() == 4u64 }, j + 1u64) using { j + 1u64 < iter.len(); j + 1u64 <= 18446744073709551615u64; };
                    solve();
                }
                have forall (j: usize) { j < iter.after_next().len() implies iter.after_next().nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.after_next().len() + j) * 4u64 } by {
                    intro(); intro();
                    have j < iter.len() - 1u64;
                    apply(chunks_exact::nth_after_next(iter, j));
                    have j + 1u64 < iter.len();
                    have j + 1u64 <= 18446744073709551615u64;
                    instantiate(forall (j: usize) { j < iter.len() implies iter.nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len() + j) * 4u64 }, j + 1u64) using { j + 1u64 < iter.len(); j + 1u64 <= 18446744073709551615u64; };
                    have bytes.len() / 4u64 - iter.after_next().len() + j == bytes.len() / 4u64 - iter.len() + (j + 1u64);
                    solve();
                }
                have (bytes.len() / 4u64 - iter.len()) * 4u64 + 3u64 < bytes.len();
                mark taken;
                step_until(read(0));
                have chunk == bytes + (bytes.len() / 4u64 - at(taken, iter.len())) * 4u64;
                have chunk_len == 4u64;
                have bytes.len() / 4u64 - at(taken, iter.len()) <= 2305843009213693951u64;
                have to_integer((bytes.len() / 4u64 - at(taken, iter.len())) * 4u64) == to_integer(bytes.len() / 4u64 - at(taken, iter.len())) * 4;
                have to_integer((bytes.len() / 4u64 - at(taken, iter.len())) * 4u64) + 3 < to_integer(bytes.len());
                have to_integer((bytes.len() / 4u64 - at(taken, iter.len())) * 4u64) < to_integer(bytes.len());
                have to_integer((bytes.len() / 4u64 - at(taken, iter.len())) * 4u64 + 3u64) < to_integer(bytes.len());
                step_until(loop(0).back_edge());
                have iter == at(taken, iter.after_next());
                have iter.len() == at(taken, iter.len()) - 1u64;
                have at(taken, iter.len()) <= bytes.len() / 4u64;
                have 0u64 < at(taken, iter.len());
                have iter.len() < at(taken, iter.len());
                have iter.len() <= bytes.len() / 4u64;
                have forall (j: usize) { j < iter.len() implies iter.nth(j).len() == 4u64 } by {
                    rewrite(iter == at(taken, iter.after_next()));
                    assumption();
                }
                have forall (j: usize) { j < iter.len() implies iter.nth(j).as_ptr() == bytes + (bytes.len() / 4u64 - iter.len() + j) * 4u64 } by {
                    rewrite(iter == at(taken, iter.after_next()));
                    assumption();
                }
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
