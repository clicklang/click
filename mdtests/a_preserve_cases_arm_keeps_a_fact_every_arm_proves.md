# A `preserve` cases arm keeps a fact every arm proves

The loop of
`a_preserve_cases_rejoin_keeps_only_the_facts_every_arm_proved.md`, with one
more `have` in each arm: the invariant at the next iteration, the same
proposition in every arm. It survives the rejoin, so the rejoined path's back
edge closes.

```c filename=a_preserve_cases_arm_keeps_a_fact_every_arm_proves.c
unsigned long f(unsigned long b)
{
	int i = 0;

	while (b >> 32) {
		b = b / 1000;
		i++;
	}
	return b;
}
```

```click
verifying "a_preserve_cases_arm_keeps_a_fact_every_arm_proves.c";
uint64 f(uint64 b) {
    requires 1u64 <= b;
    requires b <= 18446744073709u64;
    ensures true;
} by {
    execute_until(loop(0));
    loop {
        decreases b;
        invariant 1u64 <= b;
        invariant (i == 0 and b <= 18446744073709u64) or (i == 1 and b <= 18446744073u64) or (i == 2 and b <= 18446744u64);
        initialize by { auto(); }
        preserve by {
            have (b >> 32) != 0u64;
            have 4294967296u64 <= b by { auto(); }
            have (i == 0 and b <= 18446744073709u64) or (i == 1 and b <= 18446744073u64) by {
                cases {
                    i == 0 and b <= 18446744073709u64 => { simp(); }
                    i == 1 and b <= 18446744073u64 => { simp(); }
                    i == 2 and b <= 18446744u64 => {
                        have b < 4294967296u64 by { auto(); }
                        contradiction(4294967296u64 <= b);
                    }
                }
            }
            cases {
                i == 0 and b <= 18446744073709u64 => {
                    mark head;
                    execute_until(back_edge());
                    have 4294967296u64 <= at(head, b) by { auto(); }
                    have at(head, b) <= 18446744073709u64 by { simp(); }
                    have 1u64 <= at(head, b) / 1000u64 by { auto(); }
                    have at(head, b) / 1000u64 < at(head, b) by { auto(); }
                    have at(head, b) / 1000u64 <= 18446744073u64 by { auto(); }
                    have at(head, i) + 1 == 1 and at(head, b) / 1000u64 <= 18446744073u64 by { simp(); }
                    have (at(head, i) + 1 == 0 and at(head, b) / 1000u64 <= 18446744073709u64) or (at(head, i) + 1 == 1 and at(head, b) / 1000u64 <= 18446744073u64) or (at(head, i) + 1 == 2 and at(head, b) / 1000u64 <= 18446744u64) by { simp(); }
                    close_invariants() by { simp(); }
                }
                i == 1 and b <= 18446744073u64 => {
                    mark head;
                    execute_until(back_edge());
                    have 4294967296u64 <= at(head, b) by { auto(); }
                    have at(head, b) <= 18446744073u64 by { simp(); }
                    have 1u64 <= at(head, b) / 1000u64 by { auto(); }
                    have at(head, b) / 1000u64 < at(head, b) by { auto(); }
                    have at(head, b) / 1000u64 <= 18446744u64 by { auto(); }
                    have at(head, i) + 1 == 2 and at(head, b) / 1000u64 <= 18446744u64 by { simp(); }
                    have (at(head, i) + 1 == 0 and at(head, b) / 1000u64 <= 18446744073709u64) or (at(head, i) + 1 == 1 and at(head, b) / 1000u64 <= 18446744073u64) or (at(head, i) + 1 == 2 and at(head, b) / 1000u64 <= 18446744u64) by { simp(); }
                    close_invariants() by { simp(); }
                }
            }
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
