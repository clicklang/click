# Plain record storage in a symbolic loop

`loop.rs` constructs a fresh `Packet` on every iteration. The checked sidecar
proves `packet_walk(n) == n` for every `0 <= n <= 1000`, with entry,
preservation, exit, and termination obligations. It has no invariant about
compiler-generated liveness flags.

The Charon adapter retains record `StorageLive` as `BeginStorage`. Lowering
restarts the liveness flag for records containing only supported scalar/array
fields and no destructor. This changes no memory permissions and assumes no
loop invariant: the lowered assignment establishes the fresh lifetime before
construction. Records with `Drop` or reference fields retain the existing
checked move/drop protocol.

The frozen regression proves the symbolic loop and rejects false results,
false initialization, and a missing lower-bound premise. Adapter tests remove
the storage starts to reproduce the original failure and check that restarting
storage cannot erase a live `Drop` record. Nightly verification, expansion,
cold verification, and profiling recheck the certificate.

This fixes a prerequisite found while summarizing the unchanged Adler loop.
It does not establish that loop's input-view transfer or full checksum claim.
