# Indexed reads in comparisons with literals

A store to a separated cell leaves an indexed read unchanged inside bitwise
comparisons and `if` expressions. The proof of each fact is left to `solve`,
so expansion must identify the read and prove its preservation.

```c filename=indexed_reads_in_literal_comparisons.c
int32 g[4];

void keep_mask_disequality(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_mask_bound(int32 a[], int32 n) {
    g[0] = 1;
}

void keep_masked_condition(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
}

void keep_reversed_flag_comparison(int32 p[], int32 i, int32 j, int32 n) {
    p[i] = 9;
}
```

```click
verifying "indexed_reads_in_literal_comparisons.c";
import click::separation;

void keep_mask_disequality(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires (a[0] & 1) != 0;
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures (a[0] & 1) != 0;
    ensures g[0] == 1;
} by {
    step();
    have (a[0] & 1) != 0 by close();
}

void keep_mask_bound(int32 a[], int32 n) {
    requires 0 < n;
    requires viewable(a[0..n]);
    requires 0 < (a[0] & 1);
    requires separate(memory(a[0..n]), memory(g[0..1]));
    owns g[0..1];
    ensures 0 < (a[0] & 1);
    ensures g[0] == 1;
} by {
    step();
    have 0 < (a[0] & 1) by close();
}

void keep_masked_condition(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    requires (if (p[j] & 1) != 0 { 1 } else { 0 }) == 1;
    ensures (if (p[j] & 1) != 0 { 1 } else { 0 }) == 1;
} by {
    have contains(memory(p[i..i + 1]), memory((p + i)[0..1])) by {
        have 0 <= to_integer(i) by { close(); }
        have i <= ((i + 1) as int32) by { close() using { 0 <= i; i < n; }; }
        have contains(memory(p[i..i + 1]), memory((p + i)[0..(i + 1) - i])) by {
            apply(separation::contains_rebase(p, i, i + 1));
        }
        have 1 <= ((i + 1) - i) by { close() using { 0 <= i; i < n; }; }
        have contains(memory((p + i)[0..(i + 1) - i]), memory((p + i)[0..1])) by {
            apply(separation::contains_subrange(p + i, 0, (i + 1) - i, 0, 1));
        }
        apply(separation::contains_trans(memory(p[i..i + 1]),
            memory((p + i)[0..(i + 1) - i]), memory((p + i)[0..1])));
    }
    have contains(memory(p[j..j + 1]), memory(p[j..j + 1])) by {
        apply(separation::contains_refl(memory(p[j..j + 1])));
    }
    have separate(memory((p + i)[0..1]), memory(p[j..j + 1])) by {
        apply(separation::separate_restrict(memory(p[i..i + 1]), memory(p[j..j + 1]), memory((p + i)[0..1]), memory(p[j..j + 1])));
    }
    step() by { close(); }
    have (if (p[j] & 1) != 0 { 1 } else { 0 }) == 1 by close();
}

void keep_reversed_flag_comparison(int32 p[], int32 i, int32 j, int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires i >= 0;
    requires i < n;
    requires j >= 0;
    requires j < n;
    consumes p[i..i + 1];
    views p[j..j + 1];
    requires separate(memory(p[i..i + 1]), memory(p[j..j + 1]));
    requires 1 == (if p[j] > 0 { 1 } else { 0 });
    ensures 1 == (if p[j] > 0 { 1 } else { 0 });
} by {
    have contains(memory(p[i..i + 1]), memory((p + i)[0..1])) by {
        have 0 <= to_integer(i) by { close(); }
        have i <= ((i + 1) as int32) by { close() using { 0 <= i; i < n; }; }
        have contains(memory(p[i..i + 1]), memory((p + i)[0..(i + 1) - i])) by {
            apply(separation::contains_rebase(p, i, i + 1));
        }
        have 1 <= ((i + 1) - i) by { close() using { 0 <= i; i < n; }; }
        have contains(memory((p + i)[0..(i + 1) - i]), memory((p + i)[0..1])) by {
            apply(separation::contains_subrange(p + i, 0, (i + 1) - i, 0, 1));
        }
        apply(separation::contains_trans(memory(p[i..i + 1]),
            memory((p + i)[0..(i + 1) - i]), memory((p + i)[0..1])));
    }
    have contains(memory(p[j..j + 1]), memory(p[j..j + 1])) by {
        apply(separation::contains_refl(memory(p[j..j + 1])));
    }
    have separate(memory((p + i)[0..1]), memory(p[j..j + 1])) by {
        apply(separation::separate_restrict(memory(p[i..i + 1]), memory(p[j..j + 1]), memory((p + i)[0..1]), memory(p[j..j + 1])));
    }
    step() by { close(); }
    have 1 == (if p[j] > 0 { 1 } else { 0 }) by close();
}
```

```expect
pass
```
