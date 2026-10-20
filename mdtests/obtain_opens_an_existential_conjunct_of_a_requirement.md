# obtain opens an existential conjunct of a requirement

Each leaf conjunct of a fact is itself an available fact, so the existential
in `requires n > 0 and exists (k: int32) { k < n };` opens with `obtain` as
one held alone does.

```c filename=obtain_opens_an_existential_conjunct_of_a_requirement.c
void unused(void) {}
```

```click
verifying "obtain_opens_an_existential_conjunct_of_a_requirement.c";

theorem below(n: int32) {
    requires n > 0 and exists (k: int32) { k < n };
    ensures exists (m: int32) { m < n } by {
        obtain (k: int32) { k < n };
        witness { m: k };
        assumption();
    }
}
```

```expect
pass
```
