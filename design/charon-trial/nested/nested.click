import click::integer;
verifying "nested.rs";
fn array_len() -> usize { ensures result == 8u64; }
fn array_mut() -> u8 { ensures result == 9; }

fn nested(bytes: &[u8]) -> usize {
    requires bytes.len() == 8u64;
    views bytes[0..8];
    ensures result == 0u64;
    ensures forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) };
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.v.len();
        views bytes[0u64..8u64];
        invariant bytes.len() == 8u64;
        invariant tail.len() == 0u64;
        invariant iter.chunk_size == 4u64;
        invariant iter.v.len() <= 8u64;
        invariant iter.v == bytes + (8u64 - iter.v.len());
        maintain by {
            if 4u64 <= iter.v.len() {
                have to_integer(8u64 - iter.v.len()) + 4 <= 8;
                have to_integer((8u64 - iter.v.len()) + 4u64) <= 8;
                have to_integer(8u64 - iter.v.len()) < 8;
                have to_integer(8u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes + (8u64 - iter.v.len())) + 4u64 == bytes + ((8u64 - iter.v.len()) + 4u64);
                mark taken;
                step_until(loop(1).entry);
                have chunk == bytes + (8u64 - at(taken, iter.v.len()));
                have chunk.len() == 4u64;
                have 4u64 <= at(taken, iter.v.len());
                have to_integer(loop(0).iter.v.len()) == to_integer(at(taken, iter.v.len())) - 4;
                have 8u64 - at(taken, iter.v.len()) == 4u64 - loop(0).iter.v.len();
                have chunk == bytes + (4u64 - loop(0).iter.v.len());
                have loop(0).iter.v.len() <= 4u64;
                have (4u64 - loop(0).iter.v.len()) + (4u64 - 4u64) == (4u64 - loop(0).iter.v.len());
                loop {
                    decreases iter.v.len();
                    views bytes[0u64..8u64];
                    invariant bytes.len() == 8u64;
                    invariant chunk.len() == 4u64;
                    invariant loop(0).iter.v.len() <= 4u64;
                    invariant chunk == bytes + (4u64 - loop(0).iter.v.len());
                    invariant iter.chunk_size == 2u64;
                    invariant iter.v.len() <= 4u64;
                    invariant iter.v == bytes + ((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len()));
                    maintain by {
                        if 2u64 <= iter.v.len() {
                            have to_integer((4u64 - loop(0).iter.v.len())) + to_integer(4u64 - iter.v.len()) + 2 <= 8;
                            have to_integer(((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 2u64) <= 8;
                            have to_integer((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) < 8;
                            have to_integer((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 2 <= 18446744073709551615;
                            have (bytes + ((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len()))) + 2u64 == bytes + (((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 2u64);
                            have to_integer((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 1 < 8;
                            have to_integer(((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 1u64) < 8;
                            have to_integer((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 1 <= 18446744073709551615;
                            have (bytes + ((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len()))) + 1u64 == bytes + (((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len())) + 1u64);
                            mark took;
                            step_until(loop(1).back_edge);
                            have 2u64 <= at(took, iter.v.len());
                            have to_integer(iter.v.len()) == to_integer(at(took, iter.v.len())) - 2;
                            have ((4u64 - loop(0).iter.v.len()) + (4u64 - at(took, iter.v.len()))) + 2u64 == (4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len());
                            have iter.v == bytes + ((4u64 - loop(0).iter.v.len()) + (4u64 - iter.v.len()));
                        } else {
                            step(); step(); step();
                        }
                    }
                }
                step_until(loop(0).back_edge);
                have to_integer(iter.v.len()) == to_integer(at(taken, iter.v.len())) - 4;
                have (8u64 - at(taken, iter.v.len())) + 4u64 == 8u64 - iter.v.len();
                have iter.v == bytes + (8u64 - iter.v.len());
            } else {
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    have forall (k: int32) { 0 <= k and k < 8 implies bytes[k] == old(bytes[k]) } by {
        intro() {
            intro() {
                close();
            }
        }
    }
    close();
}

fn empty_array_len() -> usize { ensures result == 0u64; }
fn medium_array_len() -> usize { ensures result == 1024u64; }
fn large_array_len() -> usize { ensures result == 1000000u64; }
fn array_read(index: usize) -> u8 {
    requires index < 8u64;
    ensures result == 7;
}
