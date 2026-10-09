# A fill loop claiming one more byte is refused

The postcondition of `a_fill_loop_over_a_size_t_range_needs_no_bound.md`
with `k <= length` in place of `k < length`. `bytes[length]` is past the
range the function owns and nothing wrote it, so the claim is refused.

```c filename=a_fill_loop_claiming_one_more_byte_is_refused.c
void fill(unsigned char *bytes, unsigned long length, unsigned char value) {
    for (unsigned long i = 0; i < length; i++) {
        bytes[i] = value;
    }
}
```

```click
verifying "a_fill_loop_claiming_one_more_byte_is_refused.c";
void fill(uint8* bytes, uint64 length, uint8 value) {
    owns bytes[0..length];
    ensures forall (k: uint64) { k <= length implies bytes[k] == value };
} by {
    execute_until(loop(0));
    loop {
        decreases length - i;
        owns bytes[0..length];
        invariant i <= length;
        invariant forall (k: uint64) { k < i implies bytes[k] == value };
        preserve by {
            mark before;
            step();
            step();
            have i <= length;
            have forall (k: uint64) { k < i implies bytes[k] == value } by {
                intro();
                intro();
                if k < at(before, i) {
                    instantiate(forall (k: uint64) { k < at(before, i) implies at(before, bytes[k]) == at(before, value) }, k) using {
                        k < at(before, i);
                    }
                    transport(at(before, bytes[k]) == at(before, value), bytes[k] == value) using {
                        at(before, bytes[k]) == at(before, value);
                        k < at(before, i);
                    }
                } else {
                    have k <= at(before, i) by {
                        arithmetic() using { k < at(before, i) + 1u64; at(before, i) < length; }
                    }
                    have k == at(before, i) by {
                        apply(uint64_le_and_not_lt_implies_eq(k, at(before, i))) using {
                            k <= at(before, i);
                            not k < at(before, i);
                        }
                    }
                    rewrite(k == at(before, i));
                    simp();
                }
            }
        }
    }
    execute();
    have at(loop(0).exit, i) == length by {
        apply(uint64_le_and_not_lt_implies_eq(at(loop(0).exit, i), length)) using {
            at(loop(0).exit, i) <= length;
            not at(loop(0).exit, i) < length;
        }
    }
    have forall (k: uint64) { k < length implies bytes[k] == value } by {
        intro();
        intro();
        have k < at(loop(0).exit, i) by {
            rewrite(at(loop(0).exit, i) == length);
            assumption();
        }
        instantiate(forall (k: uint64) { k < at(loop(0).exit, i) implies at(loop(0).exit, bytes[k]) == at(loop(0).exit, value) }, k) using {
            k < at(loop(0).exit, i);
        }
        assumption();
    }
    assumption();
    assumption();
}
```

```expect
fail: found no available fact or held instance
```
