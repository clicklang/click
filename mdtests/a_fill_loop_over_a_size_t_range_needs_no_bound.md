# A fill loop over a size_t range needs no bound

`fill` writes every byte of `bytes[0..length]`, and its contract says so
with a quantifier over the `size_t` index. Nothing bounds `length`: the
range has 64-bit bounds, the loop index is compared as a 64-bit value, and
the quantified facts are used and built at `uint64`.

The proof is written with explicit steps. The loop keeps
`forall k < i: bytes[k] == value`. After the body, an index below the old
`i` takes the old fact across the write, since `k < i` makes `bytes[k]`
another cell; an index not below it is the old `i` itself, from `k <= i`
and `not k < i`, which is the cell just written.

`a_fill_loop_claiming_one_more_byte_is_refused.md` claims the byte past
the end.

```c filename=a_fill_loop_over_a_size_t_range_needs_no_bound.c
void fill(unsigned char *bytes, unsigned long length, unsigned char value) {
    for (unsigned long i = 0; i < length; i++) {
        bytes[i] = value;
    }
}
```

```click
import click::integer;
import click::separation;

verifying "a_fill_loop_over_a_size_t_range_needs_no_bound.c";
void fill(uint8* bytes, uint64 length, uint8 value) {
    owns bytes[0..length];
    ensures forall (k: uint64) { k < length implies bytes[k] == value };
} by {
    step_until(loop(0));
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
                    };
                    have at(before, i) != k by {
                        solve() using { k < at(before, i); };
                    }
                    have at(before, separate(memory(bytes[i]), memory(bytes[k]))) by {
                        apply(separation::elements(bytes, at(before, i), k)) using {
                            at(before, i) != k;
                        };
                    }
                    have separate(loop(0).statement(0).footprint, memory(bytes[k])) by {
                        normalize() using {
                            at(before, separate(memory(bytes[i]), memory(bytes[k])));
                        };
                    }
                    have at(loop(0).statement(0).exit, bytes[k]) == at(before, bytes[k]) by {
                        transport_certificate {
                            premise 0: separate(loop(0).statement(0).footprint, memory(bytes[k]))
                                => separate(loop(0).statement(0).footprint, memory(bytes[k]));
                            preserve 0 => at(loop(0).statement(0).exit, bytes[k]) == at(before, bytes[k]);
                            conclusion 1;
                        }
                    }
                    have bytes[k] == at(loop(0).statement(0).exit, bytes[k]) by { normalize(); }
                    have bytes[k] == at(before, bytes[k]) by {
                        transport_certificate {
                            premise 0: bytes[k] == at(loop(0).statement(0).exit, bytes[k])
                                => bytes[k] == at(loop(0).statement(0).exit, bytes[k]);
                            premise 1: at(loop(0).statement(0).exit, bytes[k]) == at(before, bytes[k])
                                => at(loop(0).statement(0).exit, bytes[k]) == at(before, bytes[k]);
                            transitive 0, 1 => bytes[k] == at(before, bytes[k]);
                            conclusion 2;
                        }
                    }
                    have bytes[k] == value by {
                        rewrite(bytes[k] == at(before, bytes[k]));
                        assumption();
                    }
                    assumption();
                } else {
                    have k < at(before, i) + 1;
                    have k <= at(before, i) by {
                        solve() using { k < at(before, i) + 1; };
                    }
                    have k == at(before, i);
                    rewrite(k == at(before, i));
                    solve();
                }
            }
        }
    }
    step_until(function.exit);
    have at(loop(0).exit, i) == length;
    have forall (k: uint64) { k < length implies bytes[k] == value } by {
        intro();
        intro();
        have k < at(loop(0).exit, i) by {
            rewrite(at(loop(0).exit, i) == length);
            assumption();
        }
        instantiate(forall (k: uint64) { k < at(loop(0).exit, i) implies at(loop(0).exit, bytes[k]) == at(loop(0).exit, value) }, k) using {
            k < at(loop(0).exit, i);
        };
        assumption();
    }
    assumption();
    assumption();
}
```

```expect
pass
```
