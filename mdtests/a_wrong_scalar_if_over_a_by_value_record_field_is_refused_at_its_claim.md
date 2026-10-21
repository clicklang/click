# A wrong scalar `if` over a by-value record's fields is refused at its claim

The postcondition names `1` where `pick` returns `0`. The conditional over the
record's fields lowers (`a_scalar_if_over_a_by_value_record_field_lowers.md`),
so the claim is refused as a false goal rather than as a lowering failure.

```c filename=a_wrong_scalar_if_over_a_by_value_record_field_is_refused_at_its_claim.c
struct pair {
    uint8 flag;
    uint32 value;
};

uint32 pick(struct pair p) {
    if (p.flag != 0) {
        return p.value;
    }
    return 0;
}
```

```click
verifying "a_wrong_scalar_if_over_a_by_value_record_field_is_refused_at_its_claim.c";

uint32 pick(struct pair p) {
    ensures result == (if p.flag != 0 { p.value } else { 1 });
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
