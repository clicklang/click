# Version manager commands

`click upgrade` and the `click version` subcommands install released Click
versions and select which one the `click` launcher runs. `click add`,
`click remove` and `click languages` manage the language front ends of the
version that runs. Click looks for
a project's `.click-version` file first, then the global default, and
otherwise runs the launcher's own version.

## Synopsis

```text
usage: click upgrade
       click add <cpp|rust>
       click remove <cpp|rust>
       click languages
       click version add <VERSION|latest>
       click version use [VERSION|--unset]
       click version default [VERSION]
       click version list
       click version remove <VERSION>
```

Replace the following:

- `VERSION`: a release version such as `0.1.0`. A leading `v` is removed, so
  `v0.1.0` names the same version. After that, a version is a nonempty run of
  ASCII letters, digits, `.`, `-`, and `+` that doesn't begin with `-` or `.`,
  end with `.`, or contain `..`. Any other value fails with
  `invalid Click version`.

`click upgrade`, `click version` and each `click version` subcommand accept
`--help` or `-h` as their sole argument to print the version-manager usage
above and exit successfully without reading or changing version selections or
downloading a release. `click version use` also accepts `--unset`. Use `click --help` for the command list. A wrong argument count
prints the version-manager usage above and exits with status 1.

## Install layout

The version manager stores its state in the Click home directory. That
directory is the value of `CLICK_HOME` when it is set and nonempty;
otherwise it is `.click` under `HOME`, or under `USERPROFILE` when `HOME` is
unset. When none of these is available, the command fails and asks you to
set `CLICK_HOME`. The directory contains the following:

- `bin/click`: the launcher, placed there by `install.sh` or `install.ps1`.
- `versions/VERSION/bin/click`: one installed version. A version counts as
  installed only when this file exists.
- `versions/VERSION/frontends/rust/`: the optional pinned Rust frontend and compiler runtime.
- `versions/VERSION/frontends/cpp/`: the optional pinned C++ exporter, with
  the pinned Clang's builtin headers in `clang-resource/`.
- `default`: the global default version, written by `click version default`
  and `click upgrade`.
- `tmp/`: staging directories for each download, removed after each install.

On Windows, each executable name ends in `.exe`.

## `click upgrade`

`click upgrade` asks the GitHub API for the repository's latest release,
installs it as `click version add` does, and makes it the global default as
`click version default` does. Run again with the latest release installed, it
reports that the version is already installed and sets the default.

## `click version add`

`click version add VERSION` downloads that release for the host platform and
installs it under `versions/VERSION`. `click version add latest` first asks the
GitHub API for the repository's latest release and installs its tag.

The command downloads `clicklang-TARGET.tar.gz` and its `.sha256` file from
the release tagged `vVERSION`, checks the archive's SHA-256 digest, extracts
the archive, and copies the `click` executable it contains. `TARGET` is the
host's Rust target triple, such as `x86_64-unknown-linux-gnu` or
`aarch64-apple-darwin`; a platform without prebuilt releases fails. Downloads
use `curl` over HTTPS, so `curl` must be on `PATH`. Releases come from
`clicklang/click` unless `CLICK_RELEASE_REPOSITORY` names another GitHub
repository in `owner/name` form.

When the requested version is the launcher's own version and the running
executable is the launcher in `CLICK_HOME/bin`, the command copies the
launcher instead of downloading it.

The installed directory appears only after its executable is staged
completely. An already installed version prints
`Click VERSION is already installed.` and succeeds. A `versions/VERSION`
directory without its executable is reported as an incomplete installation;
remove it before retrying.

`click version add` and `click upgrade` also install, for the new version,
each language front end the current version has (see
[languages](#languages)). One the release does not ship for this host is
reported as a warning; the version is still installed.

## Languages

C is built into Click. C++ and Rust need a front end to prepare a lock
(`click import lock`); verifying a committed lock needs none. The front ends
are add-ons of the version the launcher runs here, the one
[version dispatch](#version-dispatch) selects: the nearest project pin, then the
global default, then the launcher's own version.

- `click add cpp` (or `c++`) installs that release's pinned C++ exporter from
  `click-cpp-frontend-TARGET.tar.gz` into `versions/VERSION/frontends/cpp`,
  where `click import lock` finds it. Its manifest must name the exporter
  version, Clang version and artifact schema this Click pins.
- `click add rust` installs that release's pinned Rust front end and compiler
  runtime from `click-rust-frontend-TARGET.tar.gz` into
  `versions/VERSION/frontends/rust`; its manifest must name the version and
  layout.

Each downloads the archive and its `.sha256`, verifies the checksum, checks the
manifest, and stages the bundle before making it visible. An existing valid
bundle is kept. The C++ bundle exists for `x86_64-unknown-linux-gnu` and
`aarch64-apple-darwin`, the Rust bundle for `x86_64-unknown-linux-gnu`; other
hosts get an unavailable-platform diagnostic. The version must be installed first.
`click add c` reports that C is built in.

`click remove cpp` or `click remove rust` deletes that front end from the
version that runs. `click languages` lists C as built in and each front end as
installed (with its version), not installed with the `click add` command to
run, or not available for this host. `click version list` also notes the front
ends each version has.

## `click version use`

`click version use` manages the project pin, a `.click-version` file that contains
one version. The launcher finds the pin by searching the current directory
and then each parent directory, and uses the nearest `.click-version` it
finds. Commit the file to share the pin with collaborators.

- `click version use` prints the nearest pin, or reports that no version is pinned.
- `click version use VERSION` writes `VERSION` to the nearest existing pin, or to
  `.click-version` in the current directory when no pin exists. The version
  must already be installed; otherwise the command fails and names the
  `click version add` command to run.
- `click version use --unset` removes the nearest pin.

## `click version default`

`click version default` manages the global default, the version the launcher runs
when no project pin applies.

- `click version default` prints the global default, or reports that none is set.
- `click version default VERSION` writes `VERSION` to `CLICK_HOME/default`. The
  version must already be installed.

## `click version list`

`click version list` lists installed versions in sorted order, one per line.
It marks the global default with `(default)` and the nearest project pin with
`(project)`. With nothing installed, it prints
`No Click versions are installed.`

## `click version remove`

`click version remove VERSION` deletes `versions/VERSION`, with any front ends
installed for it. It refuses a version that is not installed, the global
default, or the version the nearest project pin selects, naming the command
that changes that selection first.

## Version dispatch

Before it runs any other subcommand, including `--help` and `--version`,
`click` selects a version: the nearest project pin, then the global default.
When a version is selected and it differs from the running executable's
version, `click` runs `CLICK_HOME/versions/VERSION/bin/click` with the same
arguments, sets `CLICK_NO_VERSION_DISPATCH=1` in its environment, and exits
with that process's exit status, or with status 1 when it has none. When no
version is selected, or the selected version is the running one, the running
executable handles the command itself.

A selected version that isn't installed fails before the command runs, with
a diagnostic that names the `click version add` command to run. An unreadable or
invalid pin or default also fails.

`click upgrade` and `click version` never dispatch: the executable you
invoke always runs them. Dispatch is also skipped when
`CLICK_NO_VERSION_DISPATCH` is set to any value, and for an executable that
lives inside the Click source tree it was built from, such as
`target/debug/click`.

## Related pages

- [Command-line interface](index.md) lists every subcommand.
- [Environment variables](environment.md#launcher-variables) describes
  `CLICK_HOME`, `CLICK_NO_VERSION_DISPATCH`, and `CLICK_RELEASE_REPOSITORY`.
