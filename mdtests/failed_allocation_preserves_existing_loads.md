# failed allocation preserves existing loads

Registering and resolving a fresh allocation must not disturb a separately
owned buffer. This covers both the null branch and a successful allocation
that is freed without initializing it.

```c filename=failed_allocation_preserves_existing_loads.c
int32 failed_allocation_preserves_existing_loads(int32 data[], int32 length) {
    int32* fresh;
    fresh = malloc(length * 4);
    if (fresh == 0) {
        return data[0];
    }
    free(fresh);
    return data[0];
}
```

```click
verifying "failed_allocation_preserves_existing_loads.c";

int32 failed_allocation_preserves_existing_loads(int32 data[], int32 length) {
    requires 1 <= length;
    requires length <= 536870911;
    owns data[0..length];
    ensures result == old(data[0]);
    ensures forall (k: int32) {
        0 <= k and k < length implies data[k] == old(data[k])
    };
} by {
    step_until(statement(2));
    have forall (k: int32) { 0 <= k and k < length implies data[k] == old(data[k]) } by {
        intro(); intro();
        have separate(statement(1).footprint, memory(data[k])) by { normalize() using {}; }
        have data[k] == at(statement(1).entry, data[k]) by {
            transport_certificate {
                premise 0: separate(statement(1).footprint, memory(data[k]))
                    => separate(statement(1).footprint, memory(data[k]));
                preserve 0 => data[k] == at(statement(1).entry, data[k]);
                conclusion 1;
            }
        }
        rewrite(data[k] == at(statement(1).entry, data[k]));
        normalize();
    }
    if fresh == 0 {
        step_until(function.exit);
    } else {
        step_until(statement(3));
        have separate(memory(fresh[0..length]), memory(data[0..length])) by assumption();
        mark before_free;
        step();
        have forall (k: int32) { 0 <= k and k < length implies data[k] == old(data[k]) } by {
            intro(); intro();
            have separate(statement(3).footprint, memory(data[k])) by {
                normalize() using { separate(memory(fresh[0..length]), memory(data[0..length])); 0 <= k; k < length; };
            }
            have data[k] == at(before_free, data[k]) by {
                transport_certificate {
                    premise 0: separate(statement(3).footprint, memory(data[k]))
                        => separate(statement(3).footprint, memory(data[k]));
                    preserve 0 => data[k] == at(before_free, data[k]);
                    conclusion 1;
                }
            }
            instantiate(forall (k: int32) { 0 <= k and k < length implies at(before_free, data[k]) == old(data[k]) }, k) using { 0 <= k; k < length; };
            rewrite(data[k] == at(before_free, data[k]));
            assumption();
        }
        step_until(function.exit);
    }
}
```

```expect
pass
```
