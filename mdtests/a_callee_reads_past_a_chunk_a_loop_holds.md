# A callee reads past a chunk a loop holds

The loop of `a_callee_reads_inside_a_chunk_a_loop_holds.md` with the call
moved one byte on: `first_of_four(chunk + done + 1)`. At `done == 12` the
callee's four bytes end at element 17 of the chunk, past the
`views chunk[0..16]` the loop holds. The lent range `bytes[0..length]` may
well contain them, but the loop holds only its chunk, so the call is
refused.

```c filename=a_callee_reads_past_a_chunk_a_loop_holds.c
unsigned char first_of_four(const unsigned char *p) { return p[0]; }
unsigned int sum(const unsigned char *bytes, unsigned long length, unsigned long start) {
    const unsigned char *chunk = bytes + start;
    unsigned int total = 0;
    unsigned long done = 0;
    while (done <= 12) {
        total = total + first_of_four(chunk + done + 1);
        done = done + 4;
    }
    return total;
}
```

```click
verifying "a_callee_reads_past_a_chunk_a_loop_holds.c";
uint8 first_of_four(const uint8* p) {
    views p[0..4];
    ensures result == p[0];
} by { execute(); simp(); }
uint32 sum(const uint8* bytes, uint64 length, uint64 start) {
    requires start <= length;
    requires 16u64 <= length - start;
    views bytes[0..length];
    ensures result == result;
} by {
    execute_until(loop(0));
    loop {
        decreases 16u64 - done;
        views chunk[0..16];
        invariant done <= 16u64;
        preserve by {
            have done <= 12u64 by { simp(); }
            have done + 4u64 <= 16u64 by { arithmetic() using { done <= 12u64; } }
            mark head;
            execute_until(back_edge());
            have done == at(head, done) + 4u64 by { simp(); }
            have at(head, done) <= 12u64 by { simp(); }
            have done <= 16u64 by { arithmetic() using { done == at(head, done) + 4u64; at(head, done) <= 12u64; } }
            have 16u64 - done < 16u64 - at(head, done) by { arithmetic() using { done == at(head, done) + 4u64; at(head, done) <= 12u64; } }
            close_invariants();
        }
    }
    execute(); simp();
}
```

```expect
fail: stable-view
```
