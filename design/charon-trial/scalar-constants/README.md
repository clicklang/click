# Checked scalar constant trial

`lib.rs` is the unchanged source used to extract `constants.ullbc` with the
pinned Charon profile. The schema-4 `click-charon-crate-v4` envelope selects
`demo::left::read`, `demo::right::read`, `demo::entry`, `demo::wide`,
`demo::small`, and `demo::flag`.

The frozen regression imports initializer CFGs and proves `CHUNK_SIZE` is
22208 through the ordinary checked call interface. False values, deleted
initializers, and overflowing arithmetic fail verification. Corrupted global
links, types, sources, static/anonymous kinds, effects, and cyclic evaluation
are rejected. A live extraction regression also verifies the two separate
`MOD` declarations, a usize value above 32 bits, u8 arithmetic, and bool.

This subset accepts named local scalar constants with straight-line arithmetic
initializers. It does not evaluate arbitrary Rust at import time. Initializer
contracts must verify before callers use their value. Constant dependencies,
branches, references, statics, trait/generic constants, and const-fn calls
remain unsupported.
