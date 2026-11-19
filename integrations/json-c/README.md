# json-c 0.18

Click verifies the two version queries in the unchanged json-c 0.18 release,
commit [05180c1fa385eb39274cf0a17223da1b82832773][release]. The
[version proof](version.click) checks that `json_c_version_num()` returns 4608
and that `json_c_version()` returns a pointer to the five readable bytes
`0.18\0`. This extends the [0.17 version example](../../examples/jsonc-existing-source/SOURCE.md)
to a real build configuration with CMake's generated `config.h`.

## Reproduce

On x86-64 Linux with Git, CMake, GCC at `/usr/bin/gcc`, and Click on `PATH`:

```sh
git clone --branch json-c-0.18 --single-branch https://github.com/json-c/json-c.git
integrations/json-c/verify.sh json-c version
```

Set `CLICK` to an absolute path to use a particular binary. The script uses
`git archive` to extract the pinned revision to a temporary directory, leaving
the checkout untouched. Click imports the selected translation unit with the
static library build's include paths and feature defines. Its x86-64 Linux
userspace profile supplies `_REENTRANT` via `-pthread` and uses C11 and modeled
system headers. This was tested with GCC 14.2 and CMake 3.31.

## Array list

```sh
integrations/json-c/verify.sh json-c array-list
```

The [array length proof](array-list.click) verifies that
`array_list_length()` returns the stored length of a readable array list.
The import selects `array_list_length` as its only function root. This makes
Click check the original accessor and the list declaration while leaving the
unrelated allocator body outside the dependency closure.

```sh
integrations/json-c/verify.sh json-c array-index
```

The index proofs share an import lock with `array_list_get_idx` as its only
function root. Two sidecars cover the cases for the `size_t` index.

- [Out of range](array-index-out-of-range.click). When the index is at least
  the stored length, the function returns `NULL`. The proof views only
  `arr->length`.
- [In range](array-index-in-range.click). When the index is less than the
  stored length, the function returns the pointer in the selected slot.
  The proof views the length, the backing-array pointer field, and that one
  slot. Ownership of the object the pointer refers to is unnecessary.

[release]: https://github.com/json-c/json-c/tree/05180c1fa385eb39274cf0a17223da1b82832773
