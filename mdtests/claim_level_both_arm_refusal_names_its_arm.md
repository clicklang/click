# a claim-level `both` arm refusal names its arm

After the return, `both` splits the postcondition `result >= 0 and
result <= 5`. The left arm closes `result >= 0`; the right arm's `simp()`
cannot prove `x <= 5` from `x <= 10`. The refusal is that arm tactic's own,
located inside the `both` (`tactic 1 > right arm tactic 1`) the way an arm
of a `both` written in a `have` body is. A claim-level `both` used to run its
arms with no source position and report only that it proved no goal.

```c filename=claim_level_both_arm_refusal_names_its_arm.c
int32 pick(int32 x) {
    return x;
}
```

```click
verifying "claim_level_both_arm_refusal_names_its_arm.c";

int32 pick(int32 x) {
    requires 0 <= x;
    requires x <= 10;
    ensures result >= 0 and result <= 5;
} by {
    step();
    both { simp(); } and { simp(); }
}
```

```expect
fail: right arm tactic 1
```
