# Chosen C-string witness preserves an entry viewability citation

A witness length chosen from the entry readable-string fact is carried past
the local declaration: its viewable range by an extracted entry citation
and `transport`, its definedness by instantiating and transporting the
entry fact. The call to `strlen` takes the caller's borrowed string
`cstr_at(bytes, _)`.

```c filename=cstr_dynamic_choose_extract.c
uint64 read_terminator(uint8 bytes[]) {
    uint64 length;
    length = strlen(bytes);
    return length;
}
```

```click
verifying "cstr_dynamic_choose_extract.c";

uint64 read_terminator(uint8 bytes[]) {
    requires click::cstr::readable(bytes);
    views str: click::cstr::cstr_at(bytes, _);
    ensures result < 18446744073709551615u64 by {
        unfold(click::cstr::readable);
        execute_until(statement(1));
        have exists (len: uint64) {
            len < 18446744073709551615u64 and
                viewable(bytes[0..len + 1u64]) and
                forall (k: uint64) { k < len implies bytes[k] != '\0' } and
                bytes[len] == '\0' and
                forall (k: uint64) { k < len + 1u64 implies defined(bytes[k]) }
        } by {
            obtain (found_len: uint64) {
                at(function.entry,
                    found_len < 18446744073709551615u64 and
                    viewable(bytes[0..found_len + 1u64]) and
                    forall (k: uint64) { k < found_len implies bytes[k] != '\0' } and
                    bytes[found_len] == '\0' and
                    forall (k: uint64) { k < found_len + 1u64 implies defined(bytes[k]) })
            }
            witness { len: found_len };
            both {
                both {
                    both {
                        both {
                            simp();
                        } and {
                            extract(at(function.entry, viewable(bytes[0..found_len + 1u64])));
                            transport(
                                at(function.entry, viewable(bytes[0..found_len + 1u64])),
                                viewable(bytes[0..found_len + 1u64])
                            ) using {
                                at(function.entry, viewable(bytes[0..found_len + 1u64]));
                            };
                        }
                    } and {
                        simp();
                    }
                } and {
                    simp();
                }
            } and {
                extract(at(function.entry, forall (k: uint64) {
                    k < found_len + 1u64 implies defined(bytes[k])
                }));
                intro();
                intro();
                instantiate(at(function.entry, forall (k: uint64) {
                    k < found_len + 1u64 implies defined(bytes[k])
                }), k) using {
                    k < found_len + 1u64;
                };
                transport(
                    at(function.entry, defined(bytes[k])),
                    defined(bytes[k])
                ) using {
                    at(function.entry, defined(bytes[k]));
                };
            }
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
