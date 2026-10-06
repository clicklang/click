# Checked constructor and record-return fixture

`lib.rs` was extracted with the pinned Charon/compiler, optimized ULLBC,
precise drops, reconstructed fallible operations, Rust 2021, and root
`demo::entry`. The schema-4 envelope binds `click-charon-crate-v3`; source and
output paths are normalized as in production extraction. This frozen artifact
supports offline body/return proofs and negative declaration-identity tests.

The live crate regressions additionally cover module-qualified constructors,
caller-supplied fields, moves, destructor-bearing returned values, and changed
constructor bodies. The separate unchanged adler2 constructor trial verifies
the actual checksum library's `Default` and `new` bodies.
