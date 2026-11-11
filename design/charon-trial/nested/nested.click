import click::rust::slice;
import click::rust::chunks_exact;
import click::integer;
verifying "nested.rs";
fn array_len() -> usize { ensures result == 8u64; }
fn array_mut() -> u8 { ensures result == 9; }

theorem nested_offset(outer: uint64, inner: uint64) {
    requires outer <= 1u64;
    requires 1u64 <= inner;
    requires inner <= 2u64;
    ensures to_integer(((1u64 - outer) * 2u64 + (2u64 - inner)) * 2u64) < 8 by {
        if 0u64 < outer {
            have outer == 1u64;
            rewrite(outer == 1u64);
            if inner < 2u64 { have inner == 1u64; rewrite(inner == 1u64); normalize(); }
            else { have inner == 2u64; rewrite(inner == 2u64); normalize(); }
        } else {
            have outer == 0u64;
            rewrite(outer == 0u64);
            if inner < 2u64 { have inner == 1u64; rewrite(inner == 1u64); normalize(); }
            else { have inner == 2u64; rewrite(inner == 2u64); normalize(); }
        }
    }
    ensures to_integer(((1u64 - outer) * 2u64 + (2u64 - inner)) * 2u64 + 1u64) < 8 by {
        if 0u64 < outer {
            have outer == 1u64;
            rewrite(outer == 1u64);
            if inner < 2u64 { have inner == 1u64; rewrite(inner == 1u64); normalize(); }
            else { have inner == 2u64; rewrite(inner == 2u64); normalize(); }
        } else {
            have outer == 0u64;
            rewrite(outer == 0u64);
            if inner < 2u64 { have inner == 1u64; rewrite(inner == 1u64); normalize(); }
            else { have inner == 2u64; rewrite(inner == 2u64); normalize(); }
        }
    }
}

fn nested(bytes: &[u8]) -> usize {
    requires bytes.len() == 8u64;
    views bytes[0..8];
    ensures result == 0u64;
    ensures forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) };
} by {
    step_until(loop(0));
    have loop(0).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64);
    have tail_len == 0u64 by {
        apply(chunks_exact::remainder_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
        solve();
    }
    have loop(0).iter.len() == bytes.len() / 4u64 by {
        apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64));
        solve();
    }
    loop {
        decreases iter.len();
        views bytes[0..8];
        invariant bytes.len() == 8u64;
        invariant tail_len == 0u64;
        invariant iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(bytes, bytes.len()), 4u64), iterations);
        invariant to_integer(iter.len()) + iterations == to_integer(bytes.len() / 4u64);
        initialize by {
            have bytes.len() == 8u64;
            have tail_len == 0u64;
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
                have (bytes.len() / 4u64 - iter.len()) <= 1u64;
                mark taken;
                step_until(loop(1));
                have chunk == bytes + (bytes.len() / 4u64 - at(taken, iter.len())) * 4u64;
                have chunk_len == 4u64;
                have loop(0).iter == at(taken, iter.after_next());
                have loop(0).iter.len() == at(taken, iter.len()) - 1u64;
                have at(taken, iter.len()) <= 2u64;
                have loop(0).iter.len() <= 1u64;
                have bytes.len() / 4u64 - at(taken, iter.len()) == 1u64 - loop(0).iter.len();
                have chunk == bytes + (1u64 - loop(0).iter.len()) * 4u64;
                have loop(1).iter == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64);
                have loop(1).iter.len() == chunk_len / 2u64 by {
                    apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64));
                    solve();
                }
                loop {
                    decreases iter.len();
                    views bytes[0u64..8u64];
                    invariant bytes.len() == 8u64;
                    invariant chunk_len == 4u64;
                    invariant loop(0).iter.len() <= 1u64;
                    invariant chunk == bytes + (1u64 - loop(0).iter.len()) * 4u64;
                    invariant iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64), iterations);
                    invariant to_integer(iter.len()) + iterations == to_integer(chunk_len / 2u64);
                    initialize by {
                        have bytes.len() == 8u64;
                        have chunk_len == 4u64;
                        have loop(0).iter.len() <= 1u64;
                        have chunk == bytes + (1u64 - loop(0).iter.len()) * 4u64;
                        have iter == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64), iterations) by {
                            apply(chunks_exact::after_zero(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64)));
                            have iter == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64);
                            solve();
                        }
                        have to_integer(iter.len()) + iterations == to_integer(chunk_len / 2u64);
                    }
                    preserve by {
                        step(); step(); step(); step();
                        if 0u64 < iter.len() {
                            have chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64).len() == chunk_len / 2u64 by {
                                apply(chunks_exact::len_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64));
                            }
                            have iter.len() <= chunk_len / 2u64;
                            have iter.len() <= 2u64;
                            have to_integer(2u64 - iter.len()) == iterations;
                            have to_integer(2u64 - iter.len()) < to_integer(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64).len());
                            have iter.nth(0u64) == chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64).nth((2u64 - iter.len())) by {
                                apply(chunks_exact::nth_after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64), iterations, 0u64, (2u64 - iter.len())));
                                solve();
                            }
                            have iter.nth(0u64).len() == 2u64 by {
                                apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64, (2u64 - iter.len())));
                                solve();
                            }
                            have iterations < to_integer(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64).len());
                            have iter.after_next() == chunks_exact::after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64), iterations + 1) by {
                                apply(chunks_exact::after_next_after(chunks_exact::chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64), iterations));
                                solve();
                            }
                            have iter.after_next().len() == iter.len() - 1u64 by {
                                apply(chunks_exact::len_after_next(iter));
                            }
                            have 1u64 <= iter.len();
                            have to_integer(((1u64 - loop(0).iter.len()) * 2u64 + (2u64 - iter.len())) * 2u64) < 8 by {
                                apply(nested_offset(loop(0).iter.len(), iter.len()));
                            }
                            have to_integer(((1u64 - loop(0).iter.len()) * 2u64 + (2u64 - iter.len())) * 2u64 + 1u64) < 8 by {
                                apply(nested_offset(loop(0).iter.len(), iter.len()));
                            }
                            have iter.nth(0u64).as_ptr() == bytes + ((1u64 - loop(0).iter.len()) * 2u64 + (2u64 - iter.len())) * 2u64 by {
                                have iter.nth(0u64).as_ptr() == chunk + (2u64 - iter.len()) * 2u64 by {
                                    apply(chunks_exact::nth_chunks_exact(Slice<u8>::Slice(chunk, chunk_len), 2u64, (2u64 - iter.len())));
                                    solve();
                                }
                                rewrite(iter.nth(0u64).as_ptr() == chunk + (2u64 - iter.len()) * 2u64);
                                rewrite(chunk == bytes + (1u64 - loop(0).iter.len()) * 4u64);
                                if loop(0).iter.len() == 1u64 {
                                    rewrite(loop(0).iter.len() == 1u64);
                                    if iter.len() == 2u64 {
                                        rewrite(iter.len() == 2u64);
                                        normalize();
                                    } else {
                                        have iter.len() == 1u64 by { solve() using { not iter.len() == 2u64; iter.len() <= 2u64; 1u64 <= iter.len(); }; }
                                        rewrite(iter.len() == 1u64);
                                        normalize();
                                    }
                                } else {
                                    have loop(0).iter.len() == 0u64 by { solve() using { not loop(0).iter.len() == 1u64; loop(0).iter.len() <= 1u64; }; }
                                    rewrite(loop(0).iter.len() == 0u64);
                                    if iter.len() == 2u64 {
                                        rewrite(iter.len() == 2u64);
                                        normalize();
                                    } else {
                                        have iter.len() == 1u64 by { solve() using { not iter.len() == 2u64; iter.len() <= 2u64; 1u64 <= iter.len(); }; }
                                        rewrite(iter.len() == 1u64);
                                        normalize();
                                    }
                                }
                            }
                            mark took;
                            step_until(read(0));
                            have part == bytes + ((1u64 - loop(0).iter.len()) * 2u64 + (2u64 - at(took, iter.len()))) * 2u64;
                            have part_len == 2u64;
                            step_until(loop(1).back_edge());
                            have iter == at(took, iter.after_next());
                            have iter.len() == at(took, iter.len()) - 1u64;
                            have 0u64 < at(took, iter.len());
                            have iter.len() < at(took, iter.len());
                        } else {
                            step();
                        }
                    }
                }
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
    have forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) } by {
        intro(); intro(); solve();
    }
    solve();
}

fn empty_array_len() -> usize { ensures result == 0u64; }
fn medium_array_len() -> usize { ensures result == 1024u64; }
fn large_array_len() -> usize { ensures result == 1000000u64; }
fn array_read(index: usize) -> u8 {
    requires index < 8u64;
    ensures result == 7;
}
