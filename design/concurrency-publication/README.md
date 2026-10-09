# One-shot release/acquire publication

`publication.c` is the frozen C11 example for the one-shot publication
milestone of the [concurrency demo](../../issues/concurrency-demo.md). The
producer initializes an ordinary payload and release-stores a ready flag; the
consumer acquire-loads the flag until it is set and then reads the payload,
before the parent joins the producer. The intended proof shows that the
consumer reads the producer's value without requiring its polling loop to
terminate.

Click's `<stdatomic.h>` projection parses the source unchanged. No runtime
models the atomic operations yet, so no sidecar is proved here; the
publication protocol and its proofs are the next step. Do not edit the C to
fit the verifier: `tests/examples.rs` pins its digest.
