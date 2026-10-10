# Unchanged zlib Adler-32 adapter trial

The unchanged zlib 1.3.1 computation imports and proves its empty-input result
for the canonical seed 1 and a nonnull buffer. **The arbitrary-length checksum
postcondition and C/Rust result equality remain unproved.** This is the C
adapter baseline for the shared [checksum specification](../../adler32-spec.click).

`adler32.c`, `zutil.h`, `zlib.h`, and `zconf.h` are byte-for-byte upstream files
from revision `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` of
[madler/zlib](https://github.com/madler/zlib/tree/51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf).
The original zlib license is included. No implementation, loop, macro, or header
was changed. The prepared input also contains GNU C Library declarations and
inline header functions; their LGPL 2.1 license is included separately.

The locked selection uses `x86_64-linux-userspace`, LP64 little-endian layout,
unsigned plain char, C11, and GCC 14. `NO_DIVIDE` and `Z_SOLO` are undefined.
The compiler import supplies its normal POSIX profile flags. Its lock records
the driver, compiler resources, ABI probe, exact options, source closure, and
prepared bytes. Ordinary verification loads the prepared input offline and
checks original local inputs; it does not run or attest the compiler. The
producer's absolute paths in the lock and line directives are provenance,
not a requirement to check out this fixture at that path.

From the repository root:

```sh
cargo build --bins
target/debug/click verify design/charon-trial/zlib/empty.click
```

To reproduce preparation on a machine with the compiler and include paths in
`empty.click.import.json`, regenerate the lock and prepared input:

```sh
target/debug/click import lock design/charon-trial/zlib/empty.click
target/debug/click verify design/charon-trial/zlib/empty.click
```

The normal compiler-import regression copies the fixture to an unrelated
working directory, verifies the original contract and its checked expansion,
rejects a false result, and rejects a changed original header. The adapter
imports the complete selected bodies, including `len--`, `--n`, `*buf++`, and the
nested compound statements from `DO16`, even though the empty-input proof
executes no byte-processing iteration. This baseline does not claim nonempty correctness,
termination for arbitrary lengths, or matched reset/null-buffer behavior.

| Original file | SHA-256 |
| --- | --- |
| `adler32.c` | `9cd1443a24ff2a3053961695bd432035c58347386a420d3388232376ebabe211` |
| `zutil.h` | `dddb2dc7a1dc339ecf2c8e089b366f08bb731c0839c7110240d17ce731bb4fea` |
| `zlib.h` | `8a5579af72ea4f427ff00a4150f0ccb3fc5c1e4379f726e101133b1ab9fc600c` |
| `zconf.h` | `f5134250a67d57459234b63858f0d9d3ef8dcc48e9e1028d3f4fdcf6eae677ae` |
