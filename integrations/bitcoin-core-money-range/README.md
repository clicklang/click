# Bitcoin Core `MoneyRange` on a macOS host

This opt-in integration example imports the unchanged inline `MoneyRange` from
Bitcoin Core v31.1 through a real `src/policy/feerate.cpp` CMake compilation
command. The host can be Apple Silicon macOS: Clang targets x86-64 Linux using
Linux headers in `inputs/sysroot`. The setup generates a compilation database;
it does not claim to link or run Bitcoin Core binaries.

The upstream tag is pinned to commit
`9be056a8a72b624dae9623b2f7bded92c2a21c91`. The expected SHA-256 values
are `624a30c64528ce9873a1e440039cd261db81deecf14ed3003c171f7c2039ca50`
for `src/consensus/amount.h` and
`a339052701a35a484a6d84e83d257ae643da2e2b635ccf105b44edf2f2ba30e8`
for `src/policy/feerate.cpp`. Check the commit and both hashes before importing;
do not copy the function into this example.

The tested toolchain was Homebrew Clang **19.1.7**, CMake **3.31.6**, and these
Debian Bookworm x86-64 development packages extracted into `inputs/sysroot`:

| Package | Version | SHA-256 of `.deb` |
| --- | --- | --- |
| `libc6-dev` | `2.36-9+deb12u14` | `0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae` |
| `linux-libc-dev` | `6.1.176-1` | `8bb258735b9dffbb111da778ebdd024750878e435ffd9dfcadcb6762ede6b4cf` |
| `libstdc++-12-dev` | `12.2.0-14+deb12u1` | `d28def6c23630432b57cb38a4c2fd67a79d4e0484027386ca6e8d6005c3d7a73` |
| `libgcc-12-dev` | `12.2.0-14+deb12u1` | `d720259380a84f2ffc6fe516eff5cbe9c8a005138e8d6a5748747ba4b3404a82` |
| `libboost1.74-dev` | `1.74.0+ds1-21` | `ba14fe04d7f138f874bd3ab3a20c4fd1e9f654e271449b8f3e48d20f942dbb93` |

Put the unmodified checkout at `inputs/bitcoin-src`, the extracted development
packages at `inputs/sysroot`, and use `inputs/bitcoin-build` for the CMake
build directory. From the repository root, generate the compilation database:

```sh
cmake -S integrations/bitcoin-core-money-range/inputs/bitcoin-src \
  -B integrations/bitcoin-core-money-range/inputs/bitcoin-build \
  -DCMAKE_TOOLCHAIN_FILE="$PWD/integrations/bitcoin-core-money-range/linux-x86_64-clang19.cmake" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DBoost_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/Boost-1.74.0" \
  -Dboost_headers_DIR="$PWD/integrations/bitcoin-core-money-range/inputs/sysroot/usr/lib/x86_64-linux-gnu/cmake/boost_headers-1.74.0" \
  -DBUILD_BITCOIN_BIN=OFF -DBUILD_DAEMON=OFF -DBUILD_CLI=OFF \
  -DBUILD_TX=OFF -DBUILD_UTIL=OFF -DBUILD_TESTS=OFF -DBUILD_BENCH=OFF \
  -DBUILD_GUI=OFF -DBUILD_KERNEL_LIB=OFF -DBUILD_UTIL_CHAINSTATE=OFF \
  -DENABLE_WALLET=OFF -DENABLE_IPC=OFF -DWITH_ZMQ=OFF
```

The generated `compile_commands.json` must contain one
`src/policy/feerate.cpp` command with `--target=x86_64-unknown-linux-gnu`,
`-std=c++20`, and no verifier-specific exception or RTTI overrides. The
toolchain file supplies the Linux sysroot, standard-library include paths, and
Clang resource directory needed by both the compiler driver and LibTooling.
Some CMake link probes warn because this header-only setup does not install a
Linux runtime; successful configuration and the selected compile command, not
a binary build, are the setup requirements.

Then build the pinned exporter and explicitly refresh the local lock:

```sh
scripts/build-cpp-exporter.sh
cargo run --bin click -- import lock integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- verify integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- profile integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- audit integrations/bitcoin-core-money-range/MoneyRange.click
cargo run --bin click -- expand --claim MoneyRange.contract integrations/bitcoin-core-money-range/MoneyRange.click
```

`MoneyRange.click.import.json` and the sidecar are versioned; this full-checkout
workflow's checkout, sysroot, compilation database, semantic artifact, and lock
remain local. The lock binds the selected command, exact source and header
bytes, all textual headers Clang opened (including sysroot and Clang resource
headers), the resolved target of each path, exporter, and observed semantic
profile. Once locked, verification loads the artifact offline without invoking
Clang. A different checkout location or toolchain command requires an explicit
refresh.

## Hermetic gate fixture

The normal `scripts/check.sh` gate also re-exports and verifies this same
`MoneyRange` sidecar without a network or a local Bitcoin checkout. Its
[`input-closure.tar.gz`](input-closure.tar.gz) contains only the 15 Bitcoin
files and 292 Linux sysroot headers observed by the pinned import, plus source
and package notices. The Bitcoin bytes were checked against the exact v31.1
Git tree; every sysroot header was matched to a member of one of the five
SHA-256-pinned Debian packages above. The gate checks the archive digest,
the unchanged selected header and translation unit, the 320-file Clang input
inventory, and re-runs semantic export and proof verification with Clang
19.1.7. No hand-copied function or precomputed semantic artifact is used.

[`feerate-command.json.in`](feerate-command.json.in) is the selected command
from the real Bitcoin CMake-generated compilation database, with only the
checkout/build/sysroot paths and pinned Clang executable/resource paths
relocated for the test machine. [`fixture-provenance.json`](fixture-provenance.json)
records the release commit, original database and import-lock identities,
archive digest, and source, package, and originating Clang executable hashes.
The gate does not rerun Bitcoin's whole CMake configuration; that remains the
opt-in full-checkout workflow above. It also does not build or run Bitcoin.

To regenerate the hermetic fixture after creating the local lock above, put
the five downloaded `.deb` archives in `inputs/packages` under the short names
shown in the table (for example `libc6-dev.deb`), then run:

```sh
python3 integrations/bitcoin-core-money-range/make-fixture.py \
  --bitcoin-src integrations/bitcoin-core-money-range/inputs/bitcoin-src \
  --sysroot integrations/bitcoin-core-money-range/inputs/sysroot \
  --packages integrations/bitcoin-core-money-range/inputs/packages \
  --lock integrations/bitcoin-core-money-range/MoneyRange.click.import.json.lock \
  --compilation-database integrations/bitcoin-core-money-range/inputs/bitcoin-build/compile_commands.json
```

Regeneration checks the Git tree, local source bytes, Debian archives and
extracted header bytes, originating Clang executable, and selected compile
flags before changing the checked-in closure. A changed archive also requires
deliberately updating the pinned digest in the gate test after review.

The sidecar also contains four one-call, modular `executes MoneyRange`
proofs. They apply the verified upstream function contract to an arbitrary
`const CAmount&` whose value is respectively `-1`, `0`, `MAX_MONEY`, or
`MAX_MONEY + 1`, and establish false, true, true, or false while returning
the reference's owned cell unchanged. These are proof-level callers: they
introduce no C++ wrapper, alternate implementation, or verifier-specific
build flag.

The gate also rejects an exclusive upper-bound claim against the unchanged
upstream function. It refuses to load the locked artifact after changes to
`amount.h`, a transitive Linux header, the CMake compile command, or the
configured profile. Selecting `MoneyRange` from a different upstream header
fails refresh, and that rejected selector cannot load the old artifact.

The gate profiles the complete upstream proof, resolves every profiled tactic
to its sidecar location, and audits all 14 smart-tactic sites. Each site is
expanded against the same locked import, the resulting certificate is checked
by ordinary verification and a retained audit session, and the expanded
claim has fewer smart sites. This covers the range contract and all four
boundary theorems without invoking Clang during verification or expansion.

This is one function under one Clang profile, not general Bitcoin Core or
Linux binary verification.

## FeeFrac value methods

The same unchanged input closure and real `feerate.cpp` compilation command
also select `FeeFrac::IsEmpty()`, `FeeFrac::operator+=`, and `FeeFrac::operator-=` from
`src/util/feefrac.h`. Its SHA-256 is
`213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9`.
No Bitcoin source, archive contents, or compiler flags were changed for these
proofs. The gate checks the existing archive digest, header digest, and the
320-file Clang inventory before verifying all five sidecars:

- `FeeFracIsEmpty.click` proves the result is exactly `size == 0`, preserving
  both fields, without requiring the application's fee/size invariant.
- `FeeFracAdd.click` proves exact addition for distinct owned objects and
  preservation of the other object's fields. Each input field is bounded to
  half its signed range, sufficient to keep both sums defined.
- `FeeFracAddSelf.click` proves the alias case `self == other`, owning each
  field once and doubling it under the same half-range bounds.
- `FeeFracSubtract.click` proves exact subtraction for distinct owned objects
  and preserves the other object's fields, under the half-range input bounds.
- `FeeFracSubtractSelf.click` proves both fields become zero for `self == other`
  over their entire signed ranges, owning each field once without range bounds.

After the full-checkout setup above, lock and verify each of these sidecars
with the same commands used for `MoneyRange`. Their adjacent import configs
select the exact upstream method; their proof interfaces use an explicit
receiver and the names `FeeFrac_IsEmpty` and `FeeFrac_operator_add_assign`.
Exceptions and RTTI remain enabled in the real command. Unselected templates,
constructors, wide-integer helpers, and other methods do not enter the proof
graph; the whole record layout and selected method bodies do.

The [synthetic value-method fixtures](../../tests/fixtures/cpp-verification/value-methods/)
separately verify source callers using both `value += value` and
`value.operator+=(value)`, with an unrelated owned cell framed unchanged.
They also check expansion/reverification and retained audit sessions, and
reject false results, incorrect sums, missing field authority, and missing
overflow bounds. Artifact regressions reject const-receiver writes and
const-to-mutable argument conversion independently of Clang's source checks.

These are bounded value-method proofs, not verification of all `FeeFrac`, fee
rounding, `CFeeRate`, or Bitcoin Core.

The [subtraction caller fixture](../../tests/fixtures/cpp-verification/subtract-methods/)
checks that self-subtraction preserves unrelated caller memory. The
[signed arithmetic fixtures](../../tests/fixtures/cpp-verification/signed-arithmetic/)
check quotient/remainder contracts, overflow and zero-divisor rejection, C++20
signed narrowing and Boolean conversion, and Bitcoin's correction expression
for concrete rounding cases with a signed 64-bit dividend. They do not prove
upstream `FeeFrac::Div` or `EvaluateFeeDown/Up`: this pinned compiler profile
uses `__int128` for the former and a templated unsigned fast path for the latter.


## Wide fee product

[`FeeFracMul.click`](FeeFracMul.click) selects the unchanged `FeeFrac::Mul`
from the same v31.1 header, archive, and x86-64 Linux compilation command.
Its header SHA-256 remains
`213a97d13eb82b34831466febcff24f4c20879603f36fc6edd894b89000f7ab9`.
The actual body is `return __int128{a} * b;`; the wide path is selected by
`__SIZEOF_INT128__`, with no fallback or source rewrite.

The sidecar explicitly states the complete signed 64-bit and 32-bit observer
ranges. Two `integer_product_bounds` certificates then establish the native
128-bit product bounds before execution. The result equals the exact
mathematical product `to_integer(a) * to_integer(b)`, rather than the
potentially overflowing narrow machine expression `to_integer(a * b)`.
These requirements cover the full input ranges; the proof currently states
those type bounds instead of inferring them automatically.

The hermetic gate checks the 320-file closure, fresh semantic export, ordinary
verification, expansion/reverification, and retained audit. It rejects false
products, missing named bounds, and execution without native product bounds.
The [synthetic modular caller](../../tests/fixtures/cpp-verification/scalar-braces/braces.cpp)
uses the same helper body and preserves unrelated owned narrow memory.
It is caller-composition coverage, not an added Bitcoin wrapper.

The next selected upstream helper is the unchanged `FeeFrac::Div`:

```cpp
Assume(d > 0);
int64_t quot = n / d;
int32_t mod = n % d;
return quot + ((mod > 0) - (mod && round_down));
```

The missing-contract refusal keeps this source out of the admitted profile.
A consteval-only regression pins `util/check.h` (SHA-256
`82705f6150e57b4de9123d22b3820f60f6f75f58c1c8b9fbff78863afca816a7`)
and admits the real template, Boolean temporary, discarded reference return,
and forced `std::source_location::current()`, then rejects the runtime
string-view argument.

The new `checked_boolean_statement_with_literal_metadata` opt-in regression
imports and lowers the complete unchanged `FeeFrac::Div`. Its separate
`literal_constructor` descriptor names
`std::basic_string_view::basic_string_view` and pins the unchanged sysroot header
`sysroot/usr/include/c++/12/string_view` to SHA-256
`9b1a575ffad1e8575cd6fc1c9a24b0cdde3793275be431726cc9c1b178a8733c`.
The artifact retains `"d > 0"`, the resolved `std::basic_string_view<char>` type,
by-value binding, and constructor provenance. The source, archive, 320-file
closure, and real compiler command remain unchanged.

Bitcoin's `Assume` expands to `inline_assertion_check<false>` in `util/check.h`,
with source-location and string-view arguments and a build-dependent abort
policy. It is an evaluated library call, separate from Clang's unevaluated
`__builtin_assume`. The explicit assertion contract requires proof that the
condition is true and assumes defined normal behavior without caller-visible
memory changes under that condition. The independently pinned constructor
contract assumes defined normal construction from admitted literals without
caller-visible memory changes. Neither library implementation is verified.
Trivial initialization and destruction are checked compiler properties; runtime
pointers, arbitrary conversions and cleanup effects remain rejected.

The integration verifies that a missing condition still fails at the named
library obligation. Plain execution from a positive narrow divisor still
requires the wide nonzero guard. An explicit checked proof now bridges
`1 <= d` to Integer and excludes `0` and `-1` to derive both wide guards
from `d > 0`; it reaches the unbounded narrow correction, including for a
zero numerator observation. These failures remain
bounded and cannot be hidden with a trivial postcondition. The shared arithmetic
foundation now includes explicit quotient/remainder
interval bounds and equality transport. Standalone C++ narrowing proofs derive
their bounds from operand ranges and compose them with exact native observations
and checked cast identities; they are pattern coverage, not a proof of this
Bitcoin helper. Signed int32/int64 order reflection now restores native bounds
from proved Integer comparisons; standalone checked narrowing proofs compose
this bridge with cast identities and preserve a modular caller's unrelated
memory.

[`FeeFracDivBounded.click`](FeeFracDivBounded.click) now proves complete
execution safety and both Integer/native output bounds of the unchanged pinned
helper. Its joint input bounds are
`INT64_MIN * d <= n <= INT64_MAX * d`, with `0 < d <= 2147483647`.
This admits every positive int32 divisor, int128 numerators far outside int64,
and exact division at both int64 endpoints. For either value of `round_down`,
the result lies in the full native range `[INT64_MIN, INT64_MAX]`.

Both narrowing identities are derived from quotient/remainder intervals. The
remainder interval uses the divisor's maximum magnitude, so it stays inside
int32 even for the wider numerator range. A positive remainder excludes
`INT64_MAX` for the quotient, and a negative
remainder excludes `INT64_MIN`: reconstruction would otherwise contradict the
scaled input bound. Shared proof-backed `integer_upper_correction_bound` and
`integer_lower_correction_bound` lemmas establish one unit of margin only in
the relevant branch. After proving native definedness there, the shared
`int64_add_to_integer` bridge bounds each possible corrected sum;
order reflection transfers those Integer bounds back to the returned native
value. No output range is assumed. The sidecar retains the explicit pinned
library assumptions described above.

Full proof expansion reverifies; retained audit and hostile omitted input
bounds, zero divisor, false result claims and swapped cast-certificate references
have coverage. The standalone fixture retains the same correction pattern and
verifies native output bounds and unrelated memory through a modular caller.
The sidecar also proves the exact corrected quotient in each remainder-sign
case, including zero, and the defining mathematical product inequalities:

- Floor (`round_down != 0`): `result * d <= n < (result + 1) * d`.
- Ceiling (`round_down == 0`): `(result - 1) * d < n <= result * d`.

These specifications use `to_integer` observations and Integer arithmetic, so
their products and successor/predecessor expressions have no native overflow.
The shared proof-backed `integer_floor_from_remainder` and
`integer_ceiling_from_remainder` lemmas combine reconstruction, positive-divisor
remainder bounds and exact correction values. Explicit Integer distributivity
connects the corrected product; affine certificates keep complete nonlinear
terms opaque. The modular caller exports the same four inequalities and frames
untouched memory. Strict claims that fail on exact division are rejected.

This completes mathematical rounding on the stated joint bounded profile.
The negative-fee `EvaluateFeeDown/Up` composition is verified below. Positive
fees, the broader mode-specific result-fit domain and the full 96/32 contract
remain open.

## CompactSize encoded length

The same pinned v31.1 archive and unchanged `feerate.cpp` compilation command
select `GetSizeOfCompactSize` in `src/serialize.h` (SHA-256
`87a273aa8cb9aeea82cd8038bb85284a5782c8abc35f8c826eb60f1a01e06775`).
The 320-file input closure and compiler flags remain unchanged. Four sidecars
cover all uint64 values:

| Sidecar | Input range | Encoded length |
| --- | --- | --- |
| `CompactSize1.click` | 0 through 252 | 1 byte |
| `CompactSize3.click` | 253 through 65,535 | 3 bytes |
| `CompactSize5.click` | 65,536 through 4,294,967,295 | 5 bytes |
| `CompactSize9.click` | 4,294,967,296 through UINT64_MAX | 9 bytes |

Use the same lock/verify setup described above. Their configs pin unsigned
`uint64_t` aliases to `bits/stdint-uintn.h` and `bits/types.h` in the hermetic
sysroot. Pinned Clang evaluates the helper's `sizeof` and constexpr
`std::numeric_limits::max()` expressions; artifacts retain their source spans
as distinct compiler constants and lock the entire preprocessor input closure.
This is part of the compiler trust boundary, not a standard-library proof.
The gate checks ordinary verification, expansion/reverification, retained audit,
and false length claims for each range. It does not prove serialization bytes,
parsing, or round trips.


The hermetic gate now also selects the unchanged `FeeFrac::EvaluateFeeDown`
and `EvaluateFeeUp` entry points. Export retains each compiler-resolved Boolean
template instance and both wide helpers, rather than removing the fallback.
Bitcoin's evaluated `Assume(size > 0)` reads its receiver field under ordinary
memory authority; its header and literal constructor remain explicitly pinned.
`[[likely]]` preserves both branch outcomes. The gate combines the existing
verified Mul/Div sidecars with concrete caller contracts: fee 7, size 3 and
at_size 2 return 4 downward and 5 upward, preserving both receiver fields.
It checks ordinary verification, caller expansion/reverification, and rejection
of false results, missing field authority and missing size/amount premises.
These concrete fast-path claims remain source admission regressions.

[`FeeFracEvaluateNegative.click.in`](FeeFracEvaluateNegative.click.in) now supplies
symbolic caller contracts for negative fees on the unchanged wide fallback.
The hermetic tests instantiate its Down/Up mode and product inequalities, then
compose it with the existing verified Mul and Div sidecars in one prepared
project. It is a caller template, rather than a standalone sidecar with assumed
helpers; the same run proves the actual helper bodies and both caller levels.

The contract explicitly requires field `views`, a negative native fee, its
full int64 observer bounds, positive int32 size and `0 <= at_size <= size`.
Both modes preserve fee and size and prove full int64 result observer bounds.
Writing `F`, `A`, `D` and `R` for the Integer observations of fee, amount, size
and result, Down proves `R * D <= F * A < (R + 1) * D`; Up proves
`(R - 1) * D < F * A <= R * D`. These include zero amount and signed endpoints.
Existing proof bindings name the captured denominator and the Mul/Div results;
explicit Integer equality rewrites connect their bounds to the caller claim.
The template does not mention generated C++ temporary names.

The gate verifies the unchanged compiler-selected graph, expands both the
wrapper and template-instance proof, reverifies the rewrites, checks retained
verification, and rejects missing authority/domain bounds, forged Mul product
equalities and false rounding inequalities. The evaluated `Assume` contract
and compiler/library pins remain the profile described above.

Next extend these symbolic contracts to positive fees on the wide fallback,
then prove the unsigned fast paths and the broader mode-specific result-fit
domain. This does not yet verify `EvaluateFeeDown/Up` for all fees.
