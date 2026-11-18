# `exact` refuses an operand that is not a memory read

`exact(place)` names a memory read by the state it is read in
(`design/exact-reads.md`). A parameter's value is not a read of memory, so
`exact(x)` has nothing to name and is refused rather than read as `x`.

```c filename=exact_refuses_an_operand_that_is_not_a_memory_read.c
int echo(int x) { return x; }
```

```click
verifying "exact_refuses_an_operand_that_is_not_a_memory_read.c";
int32 echo(int32 x) {
    ensures result == x;
} by {
    step_until(function.exit);
    have exact(x) == x by normalize();
}
```

```expect
fail: `exact` takes a memory read, such as `p[i]` or `h->next`
```
