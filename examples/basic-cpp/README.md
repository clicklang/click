# Basic C++ verification

These synthetic, header-free C++20 examples exercise Click's Clang compiler
import. `increment.cpp` is the smallest smoke test: a reference parameter is
mutated and returned. `with_restore.cpp` verifies an RAII guard whose destructor
restores the original value after either return path, while each return value
captures the value before destruction. The `.cpp` files are the same inputs
used by the focused C++ import regressions. `with_restore_caller.cpp` preserves
the original RAII source as an exact prefix, then adds a direct caller whose
precondition starts the referenced cell at 41. Its proof uses the helper's
checked contract to show a result of 7 or 9 and a post-call cell still at 41.

[`click.project.json`](click.project.json) declares one C++ unit, `basic`:
the Clang arguments of the build and, for each source, the functions its
sidecar verifies. The committed `click.project.lock.json` and `.click/basic/`
artifacts verify offline, on any machine and after the checkout moves:

```sh
cargo run --bin click -- verify examples/basic-cpp/increment.click
cargo run --bin click -- verify examples/basic-cpp/with_restore.click
cargo run --bin click -- verify examples/basic-cpp/with_restore_caller.click
```

To refresh the lock after changing a source, build the pinned Clang exporter
and lock the project:

```sh
CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)" \
  cargo run --bin click -- import lock examples/basic-cpp
```

Click writes the compilation database it hands the exporter itself, from the
unit's arguments; there is no `compile_commands.json` to maintain.
