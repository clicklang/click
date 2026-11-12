# Multi-file C++

A synthetic C++ counterpart of [`multifile-registry`](../multifile-registry/):
one unit with two translation units and a shared header, where a verified
function in one calls functions defined in the other.

| File | Role |
| --- | --- |
| `counter.h` | Declares `counter_add` and `counter_double`; defines the inline `counter_limit` |
| `counter.cpp` | Defines `counter_add` and `counter_double` |
| `client.cpp` | `bump_then_double` calls all three through the header |
| `counter.click` | Contracts and proofs for all four functions |

`client.cpp` declares the two counter functions but does not define them, so
its export records them as external interfaces. The sidecar verifies both
sources (`verifying "client.cpp"; verifying "counter.cpp";`), and Click links
them: each external interface is bound to the definition in `counter.cpp`,
whose contract the same sidecar proves, and `bump_then_double` is checked
against those contracts. `counter_limit` is defined inline in the header and
appears in `client.cpp`'s export alone. Two sources that defined one function
differently would be refused, as would a call whose callee has neither a
linked definition nor a contract
(`linked_cpp_sources_refuse_an_unproved_callee_and_differing_definitions` in
`tests/cpp_import.rs`).

From this directory, with an installed `click`:

```sh
click verify counter.click
```

To refresh the lock after changing a source, with the pinned C++ front end
installed (`click version add VERSION --cpp`; in a checkout, or on another host,
`CLICK_CPP_EXPORTER="$(scripts/build-cpp-exporter.sh)"` instead):

```sh
click import lock
```
