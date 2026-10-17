# `cases` is refused in execution contexts

## Violated invariant

The tactic reference says of `cases` that "at an execution frontier every arm
begins from the same checked C state and continues separately", so a `cases`
written before or after `execute()` is documented as supported. Both are
refused instead, with a diagnostic that blames the context: "It reached tactic
0 (proof-level `cases`), which is not implemented in this execution context."

## Reproduction

```c
int32 f(int32 n) {
    return n;
}
```

```click
int32 f(int32 n) {
    requires n == 0 or n == 1;
    ensures result <= 1;
    ensures result >= 0;
} by {
    cases {
        n == 0 => { have n <= 1 by normalize(); }
        n == 1 => { have n <= 1 by normalize(); }
    }
    execute();
    simp();
}
```

The same refusal names tactic 1 when the `cases` is moved after `execute()`.

## Intended regression

An mdtest per context (before execution, after execution) with a `cases` on an
available disjunction whose arms each prove a fact, followed by the closing
tactics.

## Acceptance criteria

Either `cases` is supported at an execution frontier and after execution, with
the same join rule as a proof `if` (what follows is checked once: the arms
rejoin, keeping the facts every arm proved, or the split is refused), or the
reference documents that `cases` is a pure-goal tactic and the refusal says so
instead of calling the proof shape unimplemented.
