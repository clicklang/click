# A theorem `let` names its native operation in a proof step

A theorem-level `let n: int8 = v + 1;` is the native `int8` sum (decision
G2), which wraps modulo 2^8. Where a clause names `n`, and where a step of
that clause's proof does, `n` is that one sum: the `have` below states the
same fact as the clause, an `int8` value's bound. Read as C's promoted
`int32` sum, the `have` would be false at `v == 127`.

`a_proof_step_about_a_theorem_let_reads_its_native_wrap.md` is the
refused counterpart.

```click
theorem goal_native_int8(v: int8) {
    let n: int8 = v + 1;
    ensures to_integer(n) <= 127;
}

theorem have_native_int8(v: int8) {
    let n: int8 = v + 1;
    ensures to_integer(n) <= 127 by {
        have to_integer(n) <= 127;
        solve();
    }
}

theorem goal_native_uint16(v: uint16) {
    let n: uint16 = v + 1;
    ensures to_integer(n) <= 65535;
}

theorem have_native_uint16(v: uint16) {
    let n: uint16 = v + 1;
    ensures to_integer(n) <= 65535 by {
        have to_integer(n) <= 65535;
        solve();
    }
}
```

```expect
pass
```
