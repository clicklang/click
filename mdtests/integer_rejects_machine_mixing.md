# mathematical Integer rejects machine scalar mixing

A comparison of an Integer with a machine value reads as an Integer
comparison, observing the machine operand with `to_integer`. Arithmetic that
combines an Integer with a machine value has no such reading, so it is refused.

```click
theorem integer_rejects_machine_mixing(x: Integer) {
    ensures x + 1u32 == x + 1;
}
```

```expect
fail: mathematical Integer expressions cannot be compared with C values
```
