# Clean up library imports and frontend dependencies

## Goal

Verification should run against interfaces that Click defines, and should not
require third-party toolchains or system headers. The rule:

- **Standard library interfaces live in Click.** A header such as
  `<pthread.h>`, `<stdatomic.h>`, `<limits.h>`, `<string.h>`, or `<span>`
  describes a library the program calls. Click supplies its own declarations
  and a specification of what each call does. Proofs are stated against that
  interface and hold conditionally on the library implementing it, as with
  the existing [modeled pthread specification](../src/languages/c/modeled_pthread_spec.md).
  Click does not import or verify a platform's library headers or bodies to
  supply an interface.
- **Compiler import is for the program's own code.** Use the real
  preprocessor only when the headers carry code that is itself under
  verification, such as Linux's own headers with its structs, inline helpers,
  macros, and `CONFIG_*` selection. Calls that code makes to anything outside
  it still use Click-side contracts.
- **A language frontend is a separate case.** Click has no Rust or C++ type
  checker of its own, so the pinned Charon and Clang 19 exporters remain
  accepted frontends. Each runs once at `click import lock`; verification
  loads the artifact offline. Frontend-produced artifacts must still not pull
  in library implementations in place of Click interfaces.
- **The default workflow needs none of it.** `click verify` on plain C needs
  no compiler or system headers, and a C contributor can run the gate without
  installing LLVM or Charon.

## Current departures

### 1. The gate requires every frontend (done)

`scripts/check.sh` builds the C++ exporter and Charon only when their
toolchains are present, skips the suites that need a missing one, and reports
each skipped suite at the start and end of the run. CI runs everything.

### 2. glibc's `<pthread.h>` as a pthread source (done)

The modeled pthread runtime accepts its declarations only from Click's
built-in `<pthread.h>` and refuses a compiler-imported header with a
diagnostic naming the built-in one. The glibc lock fixture, its tests, and the
native-validation plan in the concurrency design records are gone; the
lookalike refusals remain.

### 3. glibc's `<limits.h>` in the cross-host C fixture (done)

`tests/fixtures/cross-host-c-import/` now includes only project-local headers,
and its lock records no system-header dependency. Click's built-in
`<limits.h>` (item 5) serves programs that need `CHAR_BIT` and friends.

### 4. libstdc++ implementation proofs in the Bitcoin Core integration

`integrations/bitcoin-core-money-range/` parses Bitcoin Core against a Debian
Bookworm sysroot (`libc6-dev`, `linux-libc-dev`, `libstdc++-12-dev`,
`libgcc-12-dev`, `libboost1.74-dev`). Several of its proofs verify the
implementation of the libstdc++ `std::span<int>` pointer/count constructor,
`back()`, and `std::to_address` taken from those headers (see the C++ section
of [`click import`](../docs/reference/cli/import.md)).

Agreed strategy (2026-10-10): the C++ standard library is an axiomatic
boundary. Unlike C, the C++ standard library is mostly header code that Clang
must parse to type-check a program, so Click does not supply replacement
headers. Instead:

- **Parse the real headers; trust none of their code.** A function declared
  in a system header is an opaque call: the exporter does not lower its
  instantiated body, and Click checks the call against its own contract, keyed
  on the standard name and signature. The cut is by file, not namespace, so a
  user's own specialization in a project header remains verified user code.
- **No contract, no proof.** A call into a system header without a Click
  contract is refused by name, never trusted silently. The catalog grows on
  demand: `std::span` and `std::to_address` first.
- **Standard-library independence.** Contracts name the standard interface,
  so a proof does not depend on whether libstdc++ or libc++ was parsed. The
  lock still records the parsed headers for parse fidelity only.
- **Abstract models, not layouts.** A `std::span<T>` is a view of
  `[data, data + size)`; proofs never depend on a library's private fields.
- **Trust statement:** proofs assume a C++ standard library implementing
  Click's contracts, as for C.

Callbacks into user code (`std::sort` comparators, `std::function`) and
throwing contracts are deferred until an example needs them.

For Bitcoin Core: keep the sysroot as parse-only input, cut at system-header
functions, give `std::span` and `std::to_address` Click contracts, verify
Bitcoin Core's own functions against them, and drop the libstdc++
implementation proofs.

### 5. Missing built-in C headers (done)

Click's preprocessor provides `<limits.h>` on every target and, for the
user-space target, declaration-only `<string.h>` (`memcpy`, `memcmp`,
`memset`) and `<stdlib.h>` (`malloc`, `calloc`, `realloc`, `free`) declaring
exactly the modeled subset, so ordinary C reaches those contracts without a
compiler import. `strlen`'s contract takes a `uint8` array, so `<string.h>`
does not declare its `const char *` prototype. Add further headers only when an
example needs them.

### 6. Documentation (done, except item 4's wording)

The [`click import`](../docs/reference/cli/import.md#interface-boundary)
page states the rule, and the C0 reference's
[system headers](../docs/reference/language/c0.md#system-headers) section
lists Click's headers with the trust statement users see: proofs assume a C
library implementing Click's interfaces as specified. The modeled pthread
runtime's assumption says the same. The `click import` page's descriptions of
the libstdc++ `std::span` proofs go with item 4.

## Not departures

- `integrations/linux-rbtree/` imports Linux's own headers for `lib/rbtree.c`;
  that is the program's own code.
- The Rust examples and `design/charon-trial/` use Charon as a frontend.
- `examples/basic-cpp/` and the `cpp-verification` fixtures use the Clang
  exporter as a frontend, with project-local headers.

## Regression

- A C-only change passes `scripts/check.sh` on a machine without LLVM 19 or
  Charon, which reports the skipped frontend suites.
- An mdtest whose C includes `<string.h>` and `<stdlib.h>` verifies a
  `memcpy` and a `malloc` without a compiler import.
- The modeled pthread runtime refuses a `pthread_create` declared by any
  header other than Click's, with a diagnostic naming the built-in header.

## Acceptance

- Items 1 through 6 are done, or a remaining one is moved to its own issue
  with the user's approval.
- No test, fixture, or example depends on a platform's C or C++ library
  headers to supply a standard interface.
- The reference documentation states the interface boundary and the default
  workflow's lack of external tool requirements.
