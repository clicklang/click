import click::cstr;
import click::format;
import click::integer;

function tmp_len(j: int32) -> uint64 {
    if j == 0 { 0u64 } else { (uint64) j + 1u64 }
}
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "a-smart-tactic-search-inside-a-have-is-reported-as-a-control-engine-bug.c";

int32 s3(uint64 size, uint32 remainder, uint32 units, char buf[], int32 len) {
    requires 9 <= len;
    requires 1u64 <= size;
    requires size <= 1023u64;
    requires remainder <= 1023u32;
    requires (units & 1u32) != 1u32 implies size <= 999u64;
    requires (units & 1u32) != 1u32 implies remainder <= 999u32;
    owns buf[0..(uint64) len];
    ensures true;
} by {
    execute_until(loop(0));
    loop {
        decreases 2 - j;
        invariant 0 <= j and j <= 2;
        invariant 1u32 <= sf_cap and sf_cap <= 1023u32;
        invariant j == 1 implies 10u32 <= sf_cap;
        invariant j == 2 implies 100u32 <= sf_cap;
        initialize by { auto(); }
        preserve by {
            mark head;
            execute_until(back_edge());
            have to_integer(at(head, sf_cap)) * 10 <= 4294967295 by { auto(); }
            apply(integer::uint32_multiply_guard_by_integer_bound(at(head, sf_cap), 10u32));
            apply(integer::uint32_multiply_to_integer(at(head, sf_cap), 10u32));
            have at(head, sf_cap) <= 99u32 by { auto(); }
            have 1u32 <= sf_cap by { auto(); }
            have sf_cap <= 1023u32 by { auto(); }
            have 10u32 <= sf_cap by { auto(); }
            have at(head, j) < 2 by {
                if at(head, j) < 2 {
                    assumption();
                } else {
                    have at(head, j) == 2 by { auto(); }
                    have 100u32 <= at(head, sf_cap) by { simp(); }
                    have 99u32 < at(head, sf_cap) by { auto(); }
                    contradiction(at(head, sf_cap) <= 99u32);
                }
            }
            have j <= 2 by { auto(); }
            have 0 <= 2 - j by { auto(); }
            have j == 2 implies 100u32 <= sf_cap by {
                intro();
                have at(head, j) == 1 by { auto(); }
                have 10u32 <= at(head, sf_cap) by { simp(); }
                have 100u32 <= sf_cap by { auto(); }
                assumption();
            }
            close_invariants() by { simp(); }
        }
    }
    branch ensuring {
        fact remainder <= 999u32;
    } then {
        have to_integer(remainder) * 1000 <= 4294967295 by { auto(); }
        apply(integer::uint32_multiply_guard_by_integer_bound(remainder, 1000u32));
        apply(integer::uint32_multiply_to_integer(remainder, 1000u32));
        have remainder * 1000u32 <= 1023000u32 by { auto(); }
        have remainder * 1000u32 >> 10 <= 999u32 by { simp(); }
        step();
        step();
    } else {
        have remainder <= 999u32 by { auto(); }
    }
    if j == 0 ensuring {
        fact remainder <= 1499u32;
    } then {
        step();
        step();
        have remainder <= 1499u32 by { auto(); }
    } else {
        if j == 1 ensuring {
            fact remainder <= 1499u32;
        } then {
            step();
            step();
            have remainder <= 1499u32 by { auto(); }
        } else {
            have 0 <= j and j <= 2 by { auto(); }
            have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
            have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
            have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
            step();
            step();
            have remainder <= 1499u32 by { auto(); }
        }
    }
    branch ensuring {
        fact remainder <= 999u32;
        fact 1u64 <= size;
        fact size <= 1024u64;
        fact (units & 1u32) != 1u32 implies size <= 1000u64;
    } then {
        step();
        step();
        have remainder <= 999u32 by { auto(); }
        have 1u64 <= size by { auto(); }
        have size <= 1024u64 by { auto(); }
        have (units & 1u32) != 1u32 implies size <= 1000u64 by {
            intro();
            have old(size) <= 999u64 by { auto(); }
            have size <= 1000u64 by { auto(); }
            assumption();
        }
    } else {
        have remainder <= 999u32 by { auto(); }
        have size <= 1024u64 by { auto(); }
        have (units & 1u32) != 1u32 implies size <= 1000u64 by {
            intro();
            have size <= 999u64 by { auto(); }
            have size <= 1000u64 by { auto(); }
            assumption();
        }
    }
    have 0 <= j and j <= 2 by { auto(); }
    if j == 0 ensuring {
        fact tmp_len(j) <= 3u64;
    } then {
        have tmp_len(j) == 0u64 by { unfold(tmp_len(j)); simp(); }
        have tmp_len(j) <= 3u64 by { auto(); }
    } else {
        if j == 1 ensuring {
            fact tmp_len(j) <= 3u64;
        } then {
            have tmp_len(j) == 2u64 by { unfold(tmp_len(j)); simp(); }
            have tmp_len(j) <= 3u64 by { auto(); }
        } else {
            have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
            have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
            have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
            have tmp_len(j) == 3u64 by { unfold(tmp_len(j)); simp(); }
            have tmp_len(j) <= 3u64 by { auto(); }
        }
    }
    have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
    branch ensuring {
        fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 };
        fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) };
        fact tmp[tmp_len(j)] == 0u8;
    } then {
        have 3u64 <= format::padded_length((uint64) remainder, 3u64) by {
            unfold(format::padded_length((uint64) remainder, 3u64));
            if format::decimal_length((uint64) remainder) < 3u64 {
                normalize() using { format::decimal_length((uint64) remainder) < 3u64; };
            } else {
                have 3u64 <= format::decimal_length((uint64) remainder) by { auto(); }
                normalize() using { 3u64 <= format::decimal_length((uint64) remainder); };
            }
        }
        step();
        have tmp[0u64] == 46u8 by { auto(); }
        have tmp[0u64] != 0u8 by { auto(); }
        have defined(tmp[0u64]) by { simp(); }
        have 0u64 < format::padded_length((uint64) remainder, 3u64) by { auto(); }
        have 1u64 + 0u64 + 1u64 < 12u64 by { normalize(); }
        have tmp[1] == format::padded_digit((uint64) remainder, 3u64, 48u8, 0u64) by {
            instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies tmp[1u64 + k] == format::padded_digit((uint64) remainder, 3u64, 48u8, k) }, 0u64);
            assumption();
        }
        apply(format::padded_digit_lower_bound((uint64) remainder, 3u64, 0u64));
        have 48u8 <= tmp[1u64] by { auto(); }
        have tmp[1u64] != 0u8 by { auto(); }
        have defined(tmp[1]) by {
            instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies defined(tmp[1u64 + k]) }, 0u64);
            assumption();
        }
        have 1u64 < format::padded_length((uint64) remainder, 3u64) by { auto(); }
        have 1u64 + 1u64 + 1u64 < 12u64 by { normalize(); }
        have tmp[2] == format::padded_digit((uint64) remainder, 3u64, 48u8, 1u64) by {
            instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies tmp[1u64 + k] == format::padded_digit((uint64) remainder, 3u64, 48u8, k) }, 1u64);
            assumption();
        }
        apply(format::padded_digit_lower_bound((uint64) remainder, 3u64, 1u64));
        have 48u8 <= tmp[2u64] by { auto(); }
        have tmp[2u64] != 0u8 by { auto(); }
        have defined(tmp[2]) by {
            instantiate(forall (k: uint64) { k < format::padded_length((uint64) remainder, 3u64) and 1u64 + k + 1u64 < 12u64 implies defined(tmp[1u64 + k]) }, 1u64);
            assumption();
        }
        if j == 1 ensuring {
            fact to_integer(tmp_len(j)) + 1 <= 18446744073709551615;
            fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 };
            fact forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) };
            fact tmp[tmp_len(j)] == 0u8;
        } then {
            mark fmt;
            step();
            transport(at(fmt, tmp[0u64]) != 0u8, tmp[0u64] != 0u8);
            transport(defined(at(fmt, tmp[0u64])), defined(tmp[0u64])) using { defined(at(fmt, tmp[0u64])); j == 1; }
            transport(at(fmt, tmp[1u64]) != 0u8, tmp[1u64] != 0u8);
            transport(defined(at(fmt, tmp[1u64])), defined(tmp[1u64])) using { defined(at(fmt, tmp[1u64])); j == 1; }
            have defined(tmp[2u64]) by { normalize() using { j == 1; }; }
            have tmp[2u64] == 0u8 by { normalize() using { j == 1; }; }
            have tmp_len(j) == 2u64 by { unfold(tmp_len(j)); simp(); }
            have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
            have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
            have forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) } by { enumerate(); }
            have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
                intro();
                intro();
                have k < 2u64 by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 2u64; }; }
                instantiate(forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 }, k);
                assumption();
            }
            have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
                intro();
                intro();
                have k < 3u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 2u64; }; }
                instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) }, k);
                assumption();
            }
        } else {
            have 0 <= j and j <= 2 by { auto(); }
            have 1 <= j by { arithmetic() using { 0 <= j; j != 0; }; }
            have 2 <= j by { arithmetic() using { 1 <= j; j != 1; }; }
            have j == 2 by { arithmetic() using { 2 <= j; j <= 2; }; }
            mark fmt;
            step();
            transport(at(fmt, tmp[0u64]) != 0u8, tmp[0u64] != 0u8);
            transport(defined(at(fmt, tmp[0u64])), defined(tmp[0u64])) using { defined(at(fmt, tmp[0u64])); j == 2; }
            transport(at(fmt, tmp[1u64]) != 0u8, tmp[1u64] != 0u8);
            transport(defined(at(fmt, tmp[1u64])), defined(tmp[1u64])) using { defined(at(fmt, tmp[1u64])); j == 2; }
            transport(at(fmt, tmp[2u64]) != 0u8, tmp[2u64] != 0u8);
            transport(defined(at(fmt, tmp[2u64])), defined(tmp[2u64])) using { defined(at(fmt, tmp[2u64])); j == 2; }
            have defined(tmp[3u64]) by { normalize() using { j == 2; }; }
            have tmp[3u64] == 0u8 by { normalize() using { j == 2; }; }
            have tmp_len(j) == 3u64 by { unfold(tmp_len(j)); simp(); }
            have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
            have forall (k: uint64) { 0u64 <= k and k < 3u64 implies tmp[k] != 0u8 } by { enumerate(); }
            have forall (k: uint64) { 0u64 <= k and k < 4u64 implies defined(tmp[k]) } by { enumerate(); }
            have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
                intro();
                intro();
                have k < 3u64 by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 3u64; }; }
                instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies tmp[k] != 0u8 }, k);
                assumption();
            }
            have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
                intro();
                intro();
                have k < 4u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 3u64; }; }
                instantiate(forall (k: uint64) { 0u64 <= k and k < 4u64 implies defined(tmp[k]) }, k);
                assumption();
            }
        }
    } else {
        have j == 0 by { auto(); }
        have tmp_len(j) == 0u64 by { unfold(tmp_len(j)); simp(); }
        have to_integer(tmp_len(j)) + 1 <= 18446744073709551615 by { auto(); }
        have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) implies tmp[k] != 0u8 } by {
            intro();
            intro();
            have false by { arithmetic() using { k < tmp_len(j); tmp_len(j) == 0u64; }; }
            contradiction(false);
        }
        have forall (k: uint64) { 0u64 <= k and k < tmp_len(j) + 1u64 implies defined(tmp[k]) } by {
            intro();
            intro();
            have k < 1u64 by { arithmetic() using { k < tmp_len(j) + 1u64; tmp_len(j) == 0u64; }; }
            have k == 0u64 by { auto(); }
            rewrite(k == 0u64);
            simp();
        }
    }
    have format::decimal_length((uint64)(uint32) size) <= 20u64 by {
        unfold(format::decimal_length((uint64)(uint32) size));
        have format::decimal_length((uint64)(uint32) size) <= 20u64 by { auto(); }
        assumption();
    }
    have to_integer(format::decimal_length((uint64)(uint32) size)) + to_integer(tmp_len(j)) <= 2147483647 by { auto(); }
    step(snprintf, { n1: tmp_len(j) });
    execute();
    simp();
}
