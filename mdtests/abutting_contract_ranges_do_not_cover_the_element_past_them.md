# abutting contract ranges do not cover the element past them

The negative twin of
[`abutting_contract_ranges_keep_each_clause_at_certification.md`](abutting_contract_ranges_keep_each_clause_at_certification.md).
Certification holds each clause's own range as loadable, and those ranges end
at `x[j]`: the read of `x[j + 1]` lies past both, so the read is refused.

```c filename=abutting_contract_ranges_do_not_cover_the_element_past_them.c
int32 read_past(int32 *x, int32 i, int32 j) {
    return x[j + 1];
}
```

```click
verifying "abutting_contract_ranges_do_not_cover_the_element_past_them.c";

int32 read_past(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 == j;
    requires j < 1000;
    views x[0..(i + 1)];
    views x[j..(j + 1)];
    ensures result == x[j + 1] by auto;
}
```

```expect
fail: missing resource fact `views x[(j + 1)]`
```
