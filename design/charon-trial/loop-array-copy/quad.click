import click::integer;
verifying "quad.rs";
fn quad::load(bytes: &[u8]) -> quad::Quad {
 requires bytes.len() == 4u64; views bytes[0..4];
 ensures result.lanes[0] == bytes[0];
 ensures result.lanes[1] == bytes[1];
 ensures result.lanes[2] == bytes[2];
 ensures result.lanes[3] == bytes[3];
}
fn quad::walk(bytes: &[u8]) -> u32 {
    requires bytes.len() == 16u64;
    views bytes[0..16];
    ensures result == 0u32;
} by {
    step_until(loop(0).entry);
    loop {
        decreases iter.v.len();
        views bytes[0..16];
        invariant bytes.len() == 16u64;
        invariant iter.chunk_size == 4u64;
        invariant iter.v.len() <= 16u64;
        invariant iter.v == bytes.as_ptr() + (16u64 - iter.v.len());
        maintain by {
            if 4u64 <= iter.v.len() {
                have to_integer(16u64 - iter.v.len()) + 4 <= 16;
                have to_integer((16u64 - iter.v.len()) + 4u64) <= 16;
                have to_integer(16u64 - iter.v.len()) < 16;
                have to_integer(16u64 - iter.v.len()) + 4 <= 18446744073709551615;
                have (bytes.as_ptr() + (16u64 - iter.v.len())) + 4u64 == bytes.as_ptr() + ((16u64 - iter.v.len()) + 4u64);
                mark taken;
                step_until(assignment(chunk, 0).entry); step(); step();
                have chunk.as_ptr() == bytes.as_ptr() + (16u64 - at(taken, iter.v.len()));
                have chunk.len() == 4u64;
                mark before;
                step_until(statement(1).statement(0).region(7).entry);
                step();
                step_until(statement(1).statement(1).region(1).entry);
                step();
                step_until(assignment(_byte, 0).entry);
                have lanes.lanes[0] == at(before, chunk[0]);
                have separate(statement(1).statement(0).region(7).footprint, memory(chunk[0])) by close();
                have at(statement(1).statement(0).region(7).exit, chunk[0]) == at(statement(1).statement(0).region(7).entry, chunk[0]) by {
                    preserve(memory(chunk[0]), statement(1).statement(0).region(7));
                }
                have separate(statement(1).statement(1).region(1).footprint, memory(chunk[0])) by close();
                have at(statement(1).statement(1).region(1).exit, chunk[0]) == at(statement(1).statement(1).region(1).entry, chunk[0]) by {
                    preserve(memory(chunk[0]), statement(1).statement(1).region(1));
                }
                have lanes.lanes[0] == chunk[0] by {
                    have chunk[0] == at(before, chunk[0]) by close();
                    rewrite(chunk[0], at(before, chunk[0]));
                    close();
                }
                have lanes.lanes[1] == at(before, chunk[1]);
                have separate(statement(1).statement(0).region(7).footprint, memory(chunk[1])) by close();
                have at(statement(1).statement(0).region(7).exit, chunk[1]) == at(statement(1).statement(0).region(7).entry, chunk[1]) by {
                    preserve(memory(chunk[1]), statement(1).statement(0).region(7));
                }
                have separate(statement(1).statement(1).region(1).footprint, memory(chunk[1])) by close();
                have at(statement(1).statement(1).region(1).exit, chunk[1]) == at(statement(1).statement(1).region(1).entry, chunk[1]) by {
                    preserve(memory(chunk[1]), statement(1).statement(1).region(1));
                }
                have lanes.lanes[1] == chunk[1] by {
                    have chunk[1] == at(before, chunk[1]) by close();
                    rewrite(chunk[1], at(before, chunk[1]));
                    close();
                }
                have lanes.lanes[2] == at(before, chunk[2]);
                have separate(statement(1).statement(0).region(7).footprint, memory(chunk[2])) by close();
                have at(statement(1).statement(0).region(7).exit, chunk[2]) == at(statement(1).statement(0).region(7).entry, chunk[2]) by {
                    preserve(memory(chunk[2]), statement(1).statement(0).region(7));
                }
                have separate(statement(1).statement(1).region(1).footprint, memory(chunk[2])) by close();
                have at(statement(1).statement(1).region(1).exit, chunk[2]) == at(statement(1).statement(1).region(1).entry, chunk[2]) by {
                    preserve(memory(chunk[2]), statement(1).statement(1).region(1));
                }
                have lanes.lanes[2] == chunk[2] by {
                    have chunk[2] == at(before, chunk[2]) by close();
                    rewrite(chunk[2], at(before, chunk[2]));
                    close();
                }
                have lanes.lanes[3] == at(before, chunk[3]);
                have separate(statement(1).statement(0).region(7).footprint, memory(chunk[3])) by close();
                have at(statement(1).statement(0).region(7).exit, chunk[3]) == at(statement(1).statement(0).region(7).entry, chunk[3]) by {
                    preserve(memory(chunk[3]), statement(1).statement(0).region(7));
                }
                have separate(statement(1).statement(1).region(1).footprint, memory(chunk[3])) by close();
                have at(statement(1).statement(1).region(1).exit, chunk[3]) == at(statement(1).statement(1).region(1).entry, chunk[3]) by {
                    preserve(memory(chunk[3]), statement(1).statement(1).region(1));
                }
                have lanes.lanes[3] == chunk[3] by {
                    have chunk[3] == at(before, chunk[3]) by close();
                    rewrite(chunk[3], at(before, chunk[3]));
                    close();
                }

                have array[0] == chunk[0];
                have array[1] == chunk[1];
                have array[2] == chunk[2];
                have array[3] == chunk[3];
                step_until(loop(0).back_edge);
                have 4u64 <= at(taken, iter.v.len());
                have to_integer(iter.v.len()) == to_integer(at(taken, iter.v.len())) - 4;
                have (16u64 - at(taken, iter.v.len())) + 4u64 == 16u64 - iter.v.len();
                have iter.v == bytes.as_ptr() + (16u64 - iter.v.len());
            } else {
                step(); step(); step();
            }
        }
    }
    step_until(function.exit);
    close();
}
