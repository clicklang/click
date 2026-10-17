# A broken composite body fact is reported as missing `false`

Soundness: not soundness. The false claim is refused; only the diagnostic is
wrong.

When a call needs `views zero_box(box)` assembled from owned pieces and the
body fact `box->value == 0` no longer holds, the refusal says the missing
pure fact is `false`. The fact is instantiated over the current memory, where
`box->value` is the stored constant 5, and the folded comparison is printed
in place of the written fact. A diagnostic must name the construct that is
missing: here the body fact `box->value == 0` of `zero_box(box)`.

## Reproduction

```c filename=a.c
struct box {
    int32 value;
};

int32 make_zero(struct box* box) {
    box->value = 0;
    return 0;
}

int32 read_zero(struct box* box) {
    return box->value;
}

int32 zero_pipeline(struct box* box) {
    int32 made;
    int32 first;
    int32 second;
    made = make_zero(box);
    box->value = 5;
    first = read_zero(box);
    second = first;
    return second;
}
```

```click
verifying "a.c";

resource zero_box(box: struct box*) {
    owns box->value;
    fact box->value == 0;
}

int32 make_zero(struct box* box) {
    consumes *box;
    produces zero_box(box);
    ensures result == 0;
} by {
    execute();
    fold(zero_box(box));
    simp();
}

int32 read_zero(struct box* box) {
    views zero_box(box);
    ensures result == 0;
} by {
    observe(zero_box(box));
    execute();
    simp();
}

int32 zero_pipeline(struct box* box) {
    consumes *box;
    produces zero_box(box);
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    unfold(zero_box(box));
    step();
    step();
}
```

`click verify` refuses tactic 6, `first = read_zero(box)`, with
`assembling views zero_box(box) from owned pieces requires an exact body
fact`, `missing pure fact`, `false`.

## Intended regression

An mdtest with the program above expecting
`fail: missing pure fact` followed by a line naming `box->value == 0` (or
`zero_box(box)`'s body fact), and not the bare `false`.

## Acceptance criteria

- The refusal names the written body fact, instantiated for the call's
  arguments, rather than its value in the current memory.
- The mdtest above is checked in and passes.
