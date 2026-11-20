---
name: project-setup
description: Set up Click in an existing C, C++, or Rust project and verify one function. Use when asked to try Click on a checkout, write click.project.json, reproduce a build for verification, or get a first sidecar to verify.
---

# Click project setup

Take the user's checkout and function name through a first verification run.
Use the project's build files and instructions to resolve setup details. Ask
for a choice only when the evidence leaves multiple relevant build variants or
the intended claim is ambiguous. If the user leaves the claim open, start with
one observable behavior on a useful input path and say what the claim covers.

## Find the function and its build

1. Find the definition, its callers or tests, and the build target that
   includes it. Record the source path, build variant, and relevant target.
2. Run `click --version`. Check the [installation instructions][install] if
   Click is missing. For compiler-backed projects, check `click capture --help`
   and `click verify --help` for capture refresh and `--locked` support.
3. Recover the selected source's real compile command. Read its entry in
   `compile_commands.json`, if present, including the working directory and
   compiler. With CMake, use the project's normal configure options and add
   `-DCMAKE_EXPORT_COMPILE_COMMANDS=ON` with a Makefiles or Ninja generator.
   For other builds, use the project's verbose build or command listing.
   Build the target or run its header-generation steps if the command relies
   on generated inputs. For Rust, identify the Cargo package, crate root,
   edition, and selected features from the actual build.
4. Check [language coverage][coverage] for the function, its types, and its
   dependencies. Keep its original source and build semantics.

## Configure the smallest relevant unit

Reuse the nearest `click.project.json` above the sidecar when it exists.
Otherwise put one at the root of the verification project. Put the sidecar
beside the source or in a directory such as `proofs/` under that project.
Resolve each `verifying` path relative to the sidecar. If the proof project is
separate from the source checkout, point the unit at the source tree with
`root` and keep the proof files in the proof project.

- **C.** For a source that works with Click's built-in preprocessor, start
  with a sidecar. If the build selects headers or macros through flags, use a
  [compiler-backed C unit][units]. The unit's `root` sets the compiler working
  directory, and source keys are relative to it. Translate paths from the
  original compile command's working directory before switching roots. If
  the command ran in a build directory, preserve its generated-header paths
  when choosing a root that contains the source. Set the compiler and
  needed environment explicitly. Preserve the order of include paths,
  forced includes, and macro operations. Omit build-output and diagnostic
  options such as `-c`, `-o <path>`, dependency-output flags, and warning
  flags, after confirming their role in that build. Check the [C compiler
  profile][c-profile] for options that affect language mode, target, or
  optimization. Treat an unsupported semantic option as a blocker until
  you can establish an equivalent supported configuration.
- **C++.** Use a [C++ unit][units] with the selected source and its
  `functions`. Carry over supported compiler arguments and the matching
  exceptions and RTTI settings. For a function defined in a header, identify
  the translation unit that includes it. List files outside the logical
  source that supply reachable declarations under `dependencies`, relative
  to the unit root. Install the release's pinned front end with
  `click add cpp` when needed.
- **Rust.** Use a [Rust unit][rust] with the crate root as its source. For a
  crate, record the edition, enabled features, files, and the qualified
  function under `crate.roots`. Install the release's pinned front end with
  `click add rust` when needed.

For C, if an unrelated function in the same file blocks import, use
[dependency-closure projection][projection] on the source entry. For
json-c's lookup function, put this entry under the unit's `sources`.

```json
"arraylist.c": {
  "projection": "dependency-closure",
  "functions": ["array_list_get_idx"]
}
```

Click keeps the declarations and bodies reachable from that function. A
refusal in one of those dependencies still applies to the selected claim.

## Verify and report the result

1. Write the contract from the original function and its callers. For
   `array_list_get_idx`, a first claim could cover the null result when the
   index is outside an otherwise valid list. Use the [first proof][first-proof]
   and [configured C example][own-project] for checked syntax.
2. Run `click verify proofs/my_function.click`, substituting the actual
   sidecar path. Verification creates or refreshes the compiler captures it
   needs. Use `click capture proofs/my_function.click` when you need to run
   capture explicitly, including when the toolchain or a header outside
   tracked inputs changes.
3. Diagnose the earliest failure. For a missing file, compiler, or build
   input, compare the capture configuration against the original build. For
   a frontend refusal, check the selected source and dependencies against
   language coverage. For a proof error, follow [proof repair][repair] from
   the reported goal and trace. Keep the claim and program intact while
   investigating.
4. Report the verified function, claim and preconditions, command, and any
   assumptions Click reports. If blocked, give the exact diagnostic and the
   input, frontend feature, or proof obligation that stopped the run. When
   the project checks in captures for offline use, keep the manifest and
   artifacts under `.click/captures/` together and check the same sidecar
   with `click verify --locked`.

[install]: https://github.com/clicklang/click#install-click
[coverage]: https://github.com/clicklang/click/blob/master/docs/reference/coverage.md
[units]: https://github.com/clicklang/click/blob/master/docs/reference/cli/capture.md#project-units
[c-profile]: https://github.com/clicklang/click/blob/master/docs/reference/cli/capture.md#validation-and-supported-profile
[projection]: https://github.com/clicklang/click/blob/master/docs/reference/cli/capture.md#dependency-closure-projection
[rust]: https://github.com/clicklang/click/blob/master/docs/reference/rust.md#locked-crates-and-qualified-declarations
[first-proof]: https://github.com/clicklang/click/blob/master/docs/concepts/first-proof.md
[own-project]: https://github.com/clicklang/click/blob/master/docs/concepts/own-project.md
[repair]: https://github.com/clicklang/click/blob/master/.agents/skills/proof-repair/SKILL.md
