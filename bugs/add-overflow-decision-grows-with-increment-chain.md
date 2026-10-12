# An add's overflow decision grows with the chain of earlier increments

The simplest straight-line code is quadratic. Each assignment
`x_k = x_(k-1) + 1` is one `step`, whose cost should not depend on how many
increments came before it, but its signed-overflow decision costs work
proportional to k.

Reproduced on master `e28770b20` with `scripts/step-scaling-hunt.py`:

```c
int32 caller(int32 x0) {        /* requires 0 <= x0 <= 1000000 */
    int32 x1; ... int32 xN;
    x1 = x0 + 1;
    x2 = x1 + 1;
    ...
    xN = x(N-1) + 1;
    return xN;                  /* ensures result == x0 + N */
}
```

```sh
python3 scripts/step-scaling-hunt.py straight_line --sizes 1,16,64,128
```

The k-th assignment step charges about 45 units for small k, 609–714 near
k = 32, and 8,433–8,826 near k = 128; the whole proof is 407,567 units at
N = 128 and mean step time grows tenfold. In a late step, 8,637 of its 8,694
units are the "int32 add overflow decision" operation: proving
`x_(k-1) + 1` cannot overflow rederives a bound through every earlier
increment.

Acceptance: a multi-size regression over `straight_line` shows each
assignment step's work and time constant in k up to logarithmic factors; the
overflow check is still decided (an unbounded `x0` is still refused); no
budget or threshold is raised.
