# An owner rewrites a byte of its C string and refolds the same length

`owns cstr_at(s, n)` holds the string's `n + 1` bytes exclusively and returns
the same instance, so the length is unchanged across the call. `poke` unfolds
the string, stores a nonzero byte inside it, restates the three memory facts
at the new state, and folds `cstr_at(s, n)` again. The terminator at `s[n]`
and every other byte carry over the store because `0 < n` places them apart
from `s[0]`.

```c filename=cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.c
void poke(uint8 *s, uint64 n) { s[0] = 'a'; }
```

```click
import click::cstr;

verifying "cstr_at_owner_rewrites_a_byte_and_refolds_the_same_length.c";

void poke(uint8* s, uint64 n) {
    owns cstr_at(s, n);
    requires 0u64 < n;
} by {
    unfold(cstr_at(s, n));
    step();
    have forall (k: uint64) { 0u64 <= k and k < n implies s[k] != '\0' } by {
        intro();
        intro();
        if k == 0u64 {
            rewrite(k == 0u64);
            simp();
        } else {
            instantiate(forall (k: uint64) { 0u64 <= k and k < n implies old(s[k]) != '\0' }, k) using {
                0u64 <= k and k < n;
            }
            transport(old(s[k]) != '\0', s[k] != '\0') using {
                old(s[k]) != '\0';
                k != 0u64;
            }
        }
    }
    have s[n] == '\0' by {
        transport(old(s[n]) == '\0', s[n] == '\0') using {
            old(s[n]) == '\0';
            0u64 < n;
        }
    }
    have forall (k: uint64) { 0u64 <= k and k < n + 1u64 implies defined(s[k]) } by {
        intro();
        intro();
        if k == 0u64 {
            rewrite(k == 0u64);
            simp();
        } else {
            instantiate(forall (k: uint64) { 0u64 <= k and k < n + 1u64 implies defined(old(s[k])) }, k) using {
                0u64 <= k and k < n + 1u64;
            }
            transport(defined(old(s[k])), defined(s[k])) using {
                defined(old(s[k]));
                k != 0u64;
            }
        }
    }
    fold(cstr_at(s, n));
    execute();
}
```

```expect
pass
```
