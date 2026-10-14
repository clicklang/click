# Version manager commands

The `install`, `use`, `default`, and `versions` subcommands install released
Click versions and select which one the `click` launcher runs. Click looks for
a project's `.click-version` file first, then the global default, and
otherwise runs the launcher's own version.

## Synopsis

```text
usage: click install <VERSION|latest>
       click use [VERSION|--unset]
       click default [VERSION]
       click versions
```

Replace the following:

- `VERSION`: a release version such as `0.1.0`. A leading `v` is removed, so
  `v0.1.0` names the same version. After that, a version is a nonempty run of
  ASCII letters, digits, `.`, `-`, and `+` that doesn't begin or end with `.`
  and doesn't contain `..`. Any other value fails with
  `invalid Click version`.

These subcommands have no options other than `--unset` and no `--help`
option; `click install --help`, for example, reads `--help` as a version. Use
`click --help` for the command list. A wrong argument count prints the
version-manager usage above and exits with status 1.

## Install layout

The version manager stores its state in the Click home directory. That
directory is the value of `CLICK_HOME` when it is set and nonempty;
otherwise it is `.click` under `HOME`, or under `USERPROFILE` when `HOME` is
unset. When none of these is available, the command fails and asks you to
set `CLICK_HOME`. The directory contains the following:

- `bin/click`: the launcher, placed there by `install.sh` or `install.ps1`.
- `versions/VERSION/bin/click`: one installed version. A version counts as
  installed only when this file exists.
- `default`: the global default version, written by `click default`.
- `tmp/`: staging directories for `click install`, removed after each install.

On Windows, each executable name ends in `.exe`.

## `click install`

`click install VERSION` downloads that release for the host platform and
installs it under `versions/VERSION`. `click install latest` first asks the
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

## `click use`

`click use` manages the project pin, a `.click-version` file that contains
one version. The launcher finds the pin by searching the current directory
and then each parent directory, and uses the nearest `.click-version` it
finds. Commit the file to share the pin with collaborators.

- `click use` prints the nearest pin, or reports that no version is pinned.
- `click use VERSION` writes `VERSION` to the nearest existing pin, or to
  `.click-version` in the current directory when no pin exists. The version
  must already be installed; otherwise the command fails and names the
  `click install` command to run.
- `click use --unset` removes the nearest pin.

## `click default`

`click default` manages the global default, the version the launcher runs
when no project pin applies.

- `click default` prints the global default, or reports that none is set.
- `click default VERSION` writes `VERSION` to `CLICK_HOME/default`. The
  version must already be installed.

## `click versions`

`click versions` lists installed versions in sorted order, one per line. It
marks the global default with `(default)` and the nearest project pin with
`(project)`. With nothing installed, it prints
`No Click versions are installed.`

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
a diagnostic that names the `click install` command to run. An unreadable or
invalid pin or default also fails.

The four version-manager subcommands never dispatch: the executable you
invoke always runs them. Dispatch is also skipped when
`CLICK_NO_VERSION_DISPATCH` is set to any value, and for an executable that
lives inside the Click source tree it was built from, such as
`target/debug/click`.

## Related pages

- [Command-line interface](index.md) lists every subcommand.
- [Environment variables](environment.md#launcher-variables) describes
  `CLICK_HOME`, `CLICK_NO_VERSION_DISPATCH`, and `CLICK_RELEASE_REPOSITORY`.
