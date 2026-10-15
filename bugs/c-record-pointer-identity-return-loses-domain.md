# A modular record-pointer identity call loses access to caller-local storage

Soundness: incomplete. A valid caller cannot read its initialized local record
through the pointer returned by an independently verified identity helper.
No false acceptance is demonstrated by this reproduction.

Priority: P2.

## Reproduction on master

Reproduced on upstream master `979df5bbd` with a freshly built CLI. Put the
following C and Click blocks in a Markdown fixture (the C block must use
`filename=identity.c`), then run `click verify <fixture.md>`:

```c
struct Pair { int first; int second; };
struct Pair *identity(struct Pair *pair) { return pair; }
int caller(void) {
    struct Pair pair = { 7, 9 };
    struct Pair *q = identity(&pair);
    return q->first;
}
```

```click
verifying "identity.c";
struct Pair* identity(struct Pair* pair) {
    views pair->first;
    ensures result == pair;
} by { execute(); simp(); }
int32 caller() {
    ensures result == 7;
} by { execute(); simp(); }
```

`caller.contract` fails at tactic 0 with `missing resource fact views q->first`
at `return q->first;`. A focused `click verify --trace-proof caller <fixture.md>`
shows the identity call establishing that `q` equals the local record's address.
Ordinary record declarations do not retain a complete-storage ownership fact,
so the symbolic returned pointer fails the subsequent resource check. A direct
local-record pointer assignment, a scalar-local identity call, and a
record-pointer parameter identity call all verify.

## Acceptance

Preserve the original C, helper resource requirement and claims. Give ordinary
automatic records the storage ownership needed by the existing modular-call and
byte-range coverage rules. Keep construction destinations from receiving that
ownership twice. Verify the original example fresh, expanded, rewritten and in
a retained session, plus access to a nonzero-offset member and writes through
the returned pointer. Missing alias guarantees, false value claims and
uninitialized field reads must still reject.

## Scope correction

The original report described recovery checkpoints `2cab205db` and `d06045be7`
and required a pointer-domain rejection control. That archived experimental
model is not active on master. Master's existing
`c0_const_pointer_fields_alias_proof_expands_and_reverifies` test explicitly
accepts the same address-equality example; changing that semantic boundary is
not part of this master storage-ownership fix. This correction does not claim
to repair or activate the archived model.
