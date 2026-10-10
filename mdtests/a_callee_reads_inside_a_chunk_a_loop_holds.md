# A callee reads inside a chunk a loop holds

The loop holds `views chunk[0..16]`, taken out of the function's
`views bytes[0..length]` at a `size_t` offset. A call in its body asks for
four bytes of the chunk. Those bytes are in the lent range because the
chunk is: the loop's view lies in `bytes[0..length]`, and the callee's
`views p[0..4]` lies in the loop's view. Both steps are checked at the
call, so the body does not have to place the four bytes in the whole range,
where they are two offsets deep.

```c filename=a_callee_reads_inside_a_chunk_a_loop_holds.c
unsigned char first_of_four(const unsigned char *p) { return p[0]; }
unsigned int sum(const unsigned char *bytes, unsigned long length, unsigned long start) {
    const unsigned char *chunk = bytes + start;
    unsigned int total = 0;
    unsigned long done = 0;
    while (done <= 12) {
        total = total + first_of_four(chunk + done);
        done = done + 4;
    }
    return total;
}
```

```click
verifying "a_callee_reads_inside_a_chunk_a_loop_holds.c";
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
            have done <= 12u64;
            have done + 4u64 <= 16u64 by { arithmetic() using { done <= 12u64; } }
            mark head;
            execute_until(back_edge());
            have done == at(head, done) + 4u64;
            have at(head, done) <= 12u64;
            have done <= 16u64 by { arithmetic() using { done == at(head, done) + 4u64; at(head, done) <= 12u64; } }
            have 16u64 - done < 16u64 - at(head, done) by { arithmetic() using { done == at(head, done) + 4u64; at(head, done) <= 12u64; } }
            close_invariants();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
