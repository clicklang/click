# An operand with a side effect is rejected

The operand is never evaluated, and Click does not model discarding its effects.

```c filename=c_builtin_constant_p_effectful_operand_rejected.c
int next(int value);

int32 flag(int32 value) {
    return __builtin_constant_p(next(value));
}
```

```click
verifying "c_builtin_constant_p_effectful_operand_rejected.c";

```

```expect
fail:c_builtin_constant_p_effectful_operand_rejected.c:4: the operand of `__builtin_constant_p` must be side-effect free
```
