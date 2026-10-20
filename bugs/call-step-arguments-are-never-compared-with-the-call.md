# Call-step arguments are never compared with the call

Soundness: soundness-adjacent. No false contract claim is known to verify:
Click takes the arguments from the lowered C call, so every fact the step adds
is about the real call, and a wrong contract (`ensures result == 0` below) is
still refused. But the proof text states a call that does not happen,
`step(g(0), { })` at `return g(x + 1);`, and Click accepts it with its own
meaning ("some call to `g` with one argument"). That is the
`soundness-adjacent` case of a meaningless claim accepted with a
Click-specific meaning: a reviewer reading the proof, or its expansion, is
told the wrong arguments.

The violated invariant: a written proof step that names program values
either matches the program or is refused. The [calls with resource
bindings](../docs/reference/tactics/index.md#calls-with-resource-bindings)
reference currently documents the gap: "The written argument expressions are
only counted: Click takes the arguments from the C call and does not compare
them with what is written. Write the call's own arguments, since expansion
reprints what is written." Expansion does reprint them, so a wrong argument
written once is copied into the checked certificate.

Fixing this changes documented behavior. If a maintainer prefers to treat
argument checking as new design work, move it to the roadmap instead.

```c filename=h.c
int g(int a) { return a; }
int f(int x) { return g(x + 1); }
```

```click
verifying "h.c";

int32 g(int32 a) {
    ensures result == a;
} by {
    execute();
    simp();
}

int32 f(int32 x) {
    requires x < 100;
    ensures result == x + 1;
} by {
    let { result: r } = step(g(0), { });
    execute();
    simp();
}
```

`click verify` prints `2 selected proofs verified`. The call is `g(x + 1)`;
the step writes `g(0)`. `click expand --claim f.ensures_0` keeps the wrong
argument in the certificate:

```text
    let { result: r } = step(g(0), {});
    step();
    have result == (x + 1) by {
        assumption();
    }
    assumption();
```

Changing the contract to `ensures result == 0;` is refused, so the real call
is what is checked.

The same holds for resource maps: in a caller whose C body is
`increment(state);`, `step(increment(0), { first: c })` verifies like
`step(increment(state), { first: c })`.

## Acceptance criteria

- The reproduction is refused at the `step(g(0), { })` line with a message
  that prints the call's actual argument (`x + 1`) beside the written one,
  and the same for `step(increment(0), { first: c })` at
  `increment(state)`.
- Written arguments that equal the call's arguments by the same comparison
  other call-site steps use (syntactic C argument, or equality by current
  facts) still verify, so existing proofs that write the call's own arguments
  are unaffected.
- Expansion never prints arguments that differ from the call's.
- The reference paragraph quoted above is replaced by the new rule.
- A regression keeps both source patterns: a `let { result: ... } =
  step(g(...), { })` with a wrong argument and a binder-map step with a wrong
  argument.
