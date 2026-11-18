# A frame rule requires jointly verified outputs

A body cannot obtain a verified transfer rule by proving the same owned cell
twice. Output custody is consumed jointly before any caller can apply the rule.

```c filename=joint_output_rule.c
int *identity(int *p) { return p; }
```

```click
verifying "joint_output_rule.c";
int32* identity(int32* p) {
    owns *p;
    produces *result;
}
```

```expect
fail: joint returned resources obligation
```
