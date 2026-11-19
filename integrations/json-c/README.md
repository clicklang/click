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

The [array length proof](array-list.click) is a pending claim. Import currently
stops at `arraylist.c:22`. json-c's CMake configuration detects `strings.h`,
and the source tries to include it if the preceding `string.h` has not set
`_STRING_H` or enabled `__USE_BSD`. glibc's `string.h` sets `_STRING_H`.
Click's modeled header leaves it unset, and Click has no modeled
`strings.h`. Testing with the glibc guard defined just for diagnosis let
preprocessing finish. The parser then stopped on the function type
declaration `typedef void(array_list_free_fn)(void *data);` at
`arraylist.h:29`.

Once that translation unit imports, `array_list_length` tests reading a field
from the actual list struct. `array_list_get_idx` is the next useful claim.
It can check that out-of-range indices return null and in-range indices
return the stored pointer.

[release]: https://github.com/json-c/json-c/tree/05180c1fa385eb39274cf0a17223da1b82832773
