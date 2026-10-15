# libc++ `std::function` input closure

`input-closure.tar.gz` holds the headers one translation unit reaches
through `#include <functional>` when compiled with libc++ for x86-64 Linux:

- `libcxx/include/` holds LLVM 19.1.7's libc++ headers, from the official
  `LLVM-19.1.7-Linux-X64` release, including the target's `__config_site`.
  `libcxx/include/c++/v1/functional` has SHA-256
  `c9fd255a9882be3803f3b2f6a8d07f2ee769986922128f46da1486e5ae7c81f9`.
- `sysroot/usr/include/` holds the glibc headers those reach, from Ubuntu
  noble's `libc6-dev` 2.39-0ubuntu8.9.
- `licenses/` holds libc++'s `LICENSE.TXT` (Apache-2.0 with LLVM
  exceptions) and `libc6-dev`'s copyright file.

The archive was built as `tests/fixtures/libcxx-span`'s was: from the exact
`clang++ -std=c++20 -stdlib=libc++ -M` dependency list of that translation
unit, with Clang's resource-directory headers left out, as `tar --sort=name
--mtime=1970-01-01 --owner=0 --group=0 --numeric-owner` piped through
`gzip -n -9`. Its SHA-256 is
`3d0597d0eea563ec3f84d23cc46ccba577f0264dc1123544f4aaafb4b9616a98`.

`tests/libcxx_functional.rs` imports callers of `std::function` with the
pinned Clang. Click models a `std::function<R(A...)>` as the callable value
it holds, never the library's record, so the library's layout is not read.
