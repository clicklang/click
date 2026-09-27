# a contract range endpoint that may overflow is refused

A clause's endpoints are C `int32` expressions. With nothing bounding `j`,
`x[j..(j + 1)]` has no end at `j == 2147483647`, so the contract entry cannot
state the range and is refused. The refusal names the undefined behavior the
requirements leave open, which a bound on `j` repairs, rather than the number
of paths the endpoint split into; and it blames that one clause, not a
supposed wait for cells another clause supplies.

See
[`abutting_contract_ranges_keep_each_clause_at_certification.md`](abutting_contract_ranges_keep_each_clause_at_certification.md)
for the same clauses under `j < 1000`.

```c filename=a_contract_range_endpoint_that_may_overflow_is_refused.c
void release(int32 *x, int32 i, int32 j) {
}
```

```click
verifying "a_contract_range_endpoint_that_may_overflow_is_refused.c";

void release(int32 *x, int32 i, int32 j) {
    requires 0 <= i;
    requires i <= j;
    consumes x[0..(i + 1)];
    consumes x[j..(j + 1)];
} by {
    execute();
    simp();
}
```

```expect
fail: segment end may have undefined behavior the facts do not rule out: signed overflow
```
