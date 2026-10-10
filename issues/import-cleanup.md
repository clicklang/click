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

### 3. glibc's `<limits.h>` in the cross-host C fixture

`tests/fixtures/cross-host-c-import/` exercises lock portability by importing
`main.c`, which includes Ubuntu's `<limits.h>`. The lock test is useful; the
library header is not. Use only project-local headers in that fixture, and
give Click a built-in `<limits.h>` (item 5) for programs that need
`CHAR_BIT` and friends.

### 4. libstdc++, glibc and Boost headers in the Bitcoin Core integration

`integrations/bitcoin-core-money-range/` builds a Debian Bookworm sysroot
(`libc6-dev`, `linux-libc-dev`, `libstdc++-12-dev`, `libgcc-12-dev`,
`libboost1.74-dev`) and runs CMake to produce a compilation database. Its lock
then binds every header Clang opened. Several of its proofs verify the
implementation of the libstdc++ `std::span<int>` pointer/count constructor,
`back()`, and `std::to_address` taken from those headers
(see the C++ section of [`click import`](../docs/reference/cli/import.md)).

Bitcoin Core's own sources are the program; `std::span` is a library
interface. Give Click a C++ standard-library interface for the subset these
proofs use (`<cstdint>`, `std::span`, `std::to_address`), verify Bitcoin
Core's functions against it, and drop the sysroot and the libstdc++
implementation proofs. The two `cpp-verification` fixtures that include a
fixture-owned `<cstdint>` should then use Click's.

### 5. Missing built-in C headers

Click's C preprocessor provides `<stdint.h>`, `<inttypes.h>`, and
`<stdbool.h>`, and for the user-space target `<stddef.h>`, `<pthread.h>`,
and `<stdatomic.h>`. Every other system include is refused, so a program
that includes `<string.h>` or `<stdlib.h>` cannot be verified as written,
although the standard library already has contracts for `memcpy`, `memcmp`,
`memset`, and `strlen`, and the kernel models `malloc`, `calloc`,
`realloc`, and `free`. Add built-in `<string.h>`, `<stdlib.h>`, and
`<limits.h>` declaring exactly the modeled subset, so ordinary C uses those
contracts without a compiler import. Add further headers only when an example
needs them.

### 6. Documentation

Document the rule above in one place in the reference (the C0 and `click
import` pages), including the trust statement users see: proofs assume a C
library implementing Click's interfaces as specified. Remove wording that
presents a locked system-header import as a step toward verifying a library.

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
