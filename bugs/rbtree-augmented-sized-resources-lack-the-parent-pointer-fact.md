# Augmented rbtree typed parent-pointer facts

Soundness: incomplete. The historical refusal came from a missing typed
parent relationship in the sized resource contracts.

The sized resources now state the masked parent word as a pointer equality,
matching `rb_at` and `ctx_at`. Equality of the packed numeric word alone gives
the tag bits and address value. The typed fact supplies the parent pointer
identity needed at a fold or a call.

The [original report](https://github.com/clicklang/click/blob/d3dbacbb7/bugs/rbtree-augmented-sized-resources-lack-the-parent-pointer-fact.md)
keeps the affected sidecars and per-case repair evidence.
The [current rbtree rerun](../roadmap/rbtree-example.md#focused-verification-on-current-master)
records the first failures on master. The selected metadata proof reaches
child naming in its fold, and the typed parent-rotation helper verifies.
Full-directory verification and expansion audit remain part of the rbtree
milestone.
