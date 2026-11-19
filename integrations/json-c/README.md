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

The [array length proof](array-list.click) is a pending claim. Preprocessing
finishes, and Click accepts the function-type typedef used for the list's
callback. The parser reaches an assignment inside an `if` condition in
`array_list_new2` at `arraylist.c:56`. That assignment writes to `arr->array`.
Click currently restricts assignment expressions to simple variables.

The array-length sidecar selects `array_list_length`, but the importer parses
the allocator too. The next step is to let the C dependency-closure importer
start from a named function. The target proof for `array_list_get_idx` is that
an out-of-range index returns null and an in-range index returns the stored
pointer.

[release]: https://github.com/json-c/json-c/tree/05180c1fa385eb39274cf0a17223da1b82832773
