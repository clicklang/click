# Returned vector lanes in a symbolic chunk loop

The unchanged `quad.rs` fixture returns a four-lane record from a byte-reading
helper, then reads its second lane inside a stored `ChunksExact` loop. The
sidecar proves every returned lane equals its corresponding chunk byte at a
symbolic loop head, and preserves the real iterator cursor and remaining count.
It covers sixteen bytes with four-byte chunks; it is a lane-result transport
regression, not an Adler checksum proof.

An exact base alias identifies the object of an interior byte read. A store to
a structurally distinct local object preserves that read even when the query
uses an offset such as `chunk + 1`. The kernel uses at most two indexed exact
alias lookups per side and grants no memory authority. This additional route
establishes whole-object separation only; unequal addresses in the same object
cannot justify multi-byte framing through it.

Normal tests reject wrong interior lanes and missing shared input authority.
Kernel tests cover missing/withdrawn alias evidence, overlapping same-object
accesses, and deterministic scaling. Nightly tests expand and independently
verify the certificate and check profiling. The next plain local-array copy
failure is recorded in `bugs/rust-loop-local-array-copy-lacks-backing.md`.
