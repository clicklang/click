# cJSON v1.7.19

Click verifies `cJSON_IsNumber` from the unchanged upstream release using
GCC in the project's C89 mode and the compiler's native header search path.

- [Null input](cjson-is-number-null.click) returns zero.
- [Readable type field](cjson-is-number-tag.click) gives exactly the result
  of comparing the low eight bits of the tag with `cJSON_Number` (8).

Both proofs share a compiler import rooted at `cJSON_IsNumber`. The script
extracts the pinned commit, runs the upstream CMake build, and constructs a
Click project from the C89, visibility, code-generation, and macro switches
used here. It supplies GCC's system include directories in their native order.

```sh
git clone --branch v1.7.19 --single-branch https://github.com/DaveGamble/cJSON.git
integrations/cjson/verify.sh cJSON
```

Use x86-64 Linux with GCC at `/usr/bin/gcc`, CMake, Python 3, and Click.
Set `CLICK` to select a specific Click binary. The [pinned source][release]
is commit `c859b25da02955fef659d658b8f324b5cde87be3`.

[release]: https://github.com/DaveGamble/cJSON/tree/c859b25da02955fef659d658b8f324b5cde87be3
