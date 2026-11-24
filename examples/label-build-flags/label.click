import click::bytes;
import click::c::string::{cstr_at};
import click::separation;

verifying "label_fit.c";
verifying "label_copy.c";

uint64 label_fit(uint64 length) {
    ensures result < 32;
    ensures result <= length;
    ensures length < 32u64 implies result == length;
    ensures 32u64 <= length implies result == 31u64;
}

uint64 label_measure(const char* src) {
    let n: uint64;
    views cstr_at(src, n);
    ensures n < 32u64 implies result == n;
    ensures 32u64 <= n implies result == 31u64;
}

uint64 label_copy(char* dst, const char* src) {
    let len: uint64;
    views cstr_at(src, len);
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..len + 1u64]));
    ensures len < 32u64 implies result == len;
    ensures 32u64 <= len implies result == 31u64;
    ensures dst[result] == '\0';
    ensures bytes::equal(dst, 0u64, src, 0u64, result);
} by {
    step();
    step();
    step();
    step();
    have 0u64 <= n by { close(); }
    have n < 32u64 by { close(); }
    have n <= len by { close(); }
    have contains(memory(dst[0u64..32u64]), memory(dst[n])) by {
        apply(separation::contains_element(dst, 0u64, 32u64, n));
    }
    have separate(memory(dst[n]), memory(src[0u64..len + 1u64])) by { close(); }
    with(cstr_at(src, len)) {
        step();
        mark copied;
        unfold(at(copied, bytes::equal(dst, 0u64, old(src), 0u64, n)));
        step();
        have bytes::equal(dst, 0u64, src, 0u64, n) by {
            unfold(bytes::equal(dst, 0u64, src, 0u64, n));
            intro(); intro();
            have separate(memory((dst as (uint8 *))[n]), memory((dst as (uint8 *))[k])) by {
                apply(separation::separate_elements(dst as (uint8 *), n, k));
            }
            have separate(statement(2).footprint, memory((dst as (uint8 *))[k])) by {
                close() using { separate(memory((dst as (uint8 *))[n]), memory((dst as (uint8 *))[k])); };
            }
            have (dst as (uint8 *))[k] == at(copied, (dst as (uint8 *))[k]) by {
                preserve(memory((dst as (uint8 *))[k]), statement(2));
            }
            instantiate(at(copied, (0u64..n).all(|j| {
                (dst as (uint8 *))[0u64 + j] == old((src as (uint8 *))[0u64 + j])
            })), k);
            have k < len + 1u64 by close() using { k < n; n <= len; };
            apply(separation::contains_element(src as (uint8 *), 0u64, len + 1u64, k));
            apply(separation::contains_subrange(dst as (uint8 *), 0u64, 32u64, 0u64, n));
            apply(separation::contains_refl(memory(src[0u64..len + 1u64])));
            apply(separation::separate_restrict(memory(dst[0u64..32u64]), memory(src[0u64..len + 1u64]),
                memory(dst[0u64..n]), memory(src[0u64..len + 1u64])));
            have contains(memory(dst[0u64..n]), statement(1).footprint) by { close(); }
            apply(separation::separate_restrict(
                memory(dst[0u64..n]), memory(src[0u64..len + 1u64]),
                statement(1).footprint, memory((src as (uint8 *))[k])
            ));
            have separate(memory(n), memory((src as (uint8 *))[k])) by { close(); }
            have separate(region(0).footprint, memory((src as (uint8 *))[k])) by {
                close() using { separate(memory(n), memory((src as (uint8 *))[k])); };
            }
            have at(region(0).exit, exact((src as (uint8 *))[k])) == old(exact((src as (uint8 *))[k])) by {
                preserve(memory((src as (uint8 *))[k]), region(0));
            }
            have separate(region(3).footprint, memory((src as (uint8 *))[k])) by {
                close() using { separate(memory(n), memory((src as (uint8 *))[k])); };
            }
            have at(region(3).exit, exact((src as (uint8 *))[k])) == at(region(3).entry, exact((src as (uint8 *))[k])) by {
                preserve(memory((src as (uint8 *))[k]), region(3));
            }
            have at(region(3).entry, exact((src as (uint8 *))[k])) == at(region(0).exit, exact((src as (uint8 *))[k])) by { close(); }
            have at(copied, exact((src as (uint8 *))[k])) == at(region(3).exit, exact((src as (uint8 *))[k])) by {
                preserve(memory((src as (uint8 *))[k]), statement(1));
            }
            apply(separation::contains_refl(memory((dst as (uint8 *))[n])));
            apply(separation::separate_restrict(
                memory((dst as (uint8 *))[n]), memory(src[0u64..len + 1u64]),
                memory((dst as (uint8 *))[n]), memory((src as (uint8 *))[k])
            ));
            have separate(statement(2).footprint, memory((src as (uint8 *))[k])) by {
                close() using { separate(memory((dst as (uint8 *))[n]), memory((src as (uint8 *))[k])); };
            }
            have (src as (uint8 *))[k] == at(copied, exact((src as (uint8 *))[k])) by {
                preserve(memory((src as (uint8 *))[k]), statement(2));
            }
            rewrite((src as (uint8 *))[k], at(copied, exact((src as (uint8 *))[k])));
            rewrite(at(copied, exact((src as (uint8 *))[k])), at(region(3).exit, exact((src as (uint8 *))[k])));
            rewrite(at(region(3).exit, exact((src as (uint8 *))[k])), at(region(3).entry, exact((src as (uint8 *))[k])));
            rewrite(at(region(3).entry, exact((src as (uint8 *))[k])), at(region(0).exit, exact((src as (uint8 *))[k])));
            rewrite(at(region(0).exit, exact((src as (uint8 *))[k])), old(exact((src as (uint8 *))[k])));
            rewrite((dst as (uint8 *))[k], at(copied, (dst as (uint8 *))[k]));
            close();
        }
        step_until(function.exit);
    }
}
