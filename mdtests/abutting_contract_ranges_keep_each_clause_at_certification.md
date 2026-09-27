# abutting contract ranges keep each clause at certification

Two memory clauses whose ranges abut, such as `x[0..(i + 1)]` and
`x[j..(j + 1)]` under `i + 1 == j`, are joined into one range `x[0..(j + 1)]`
when the contract entry's resources are normalized. The proof holds each
clause as written: its extent guards and its `viewable` fact. Certification
must authorize the same facts, and it used to derive them only from the joined
range, where `viewable(x[j..(j + 1)])` or the guard `0 <= j` needs order
reasoning through the equality. The contract context now carries each
clause's own guards and loadability, which the joined range is the union of.

The negative twins are
[`abutting_contract_ranges_do_not_cover_the_element_past_them.md`](abutting_contract_ranges_do_not_cover_the_element_past_them.md)
and
[`a_contract_range_endpoint_that_may_overflow_is_refused.md`](a_contract_range_endpoint_that_may_overflow_is_refused.md).

```c filename=abutting_contract_ranges_keep_each_clause_at_certification.c
void release(int32 *x, int32 i, int32 j) {
}

void release_to(int32 *x, int32 i, int32 j) {
}

void inspect(int32 *x, int32 i, int32 j) {
}

int32 read_second(int32 *x, int32 i, int32 j) {
    return x[j];
}
```

```click
verifying "abutting_contract_ranges_keep_each_clause_at_certification.c";

void release(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 == j;
    requires j < 1000;
    consumes x[0..(i + 1)];
    consumes x[j..(j + 1)];
} by {
    execute();
    simp();
}

void release_to(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 == j;
    requires j < 1000;
    consumes x[0..j];
    consumes x[j..(j + 1)];
} by {
    execute();
    simp();
}

void inspect(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires j == i + 1;
    requires j < 1000;
    views x[0..(i + 1)];
    views x[j..(j + 1)];
} by {
    execute();
    simp();
}

int32 read_second(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 == j;
    requires j < 1000;
    views x[0..(i + 1)];
    views x[j..(j + 1)];
    ensures result == x[j] by auto;
}
```

```expect
pass
```
