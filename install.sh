#!/bin/sh
set -eu

export LC_ALL=C

fail() {
    printf 'click installer: %s\n' "$1" >&2
    exit 1
}

repository=${CLICK_RELEASE_REPOSITORY:-clicklang/click}
case "$repository" in
    */*)
        owner=${repository%%/*}
        name=${repository#*/}
        case "$name" in */*) fail 'CLICK_RELEASE_REPOSITORY must be owner/name' ;; esac
        ;;
    *) fail 'CLICK_RELEASE_REPOSITORY must be owner/name' ;;
esac
case "$owner" in ''|*[!A-Za-z0-9._-]*) fail 'invalid GitHub owner in CLICK_RELEASE_REPOSITORY' ;; esac
case "$name" in ''|*[!A-Za-z0-9._-]*) fail 'invalid GitHub repository in CLICK_RELEASE_REPOSITORY' ;; esac

version=${CLICK_VERSION:-latest}
if [ "$version" = latest ]; then
    metadata=$(curl --fail --location --silent --show-error \
        --proto '=https' --tlsv1.2 --connect-timeout 15 --max-time 60 \
        --header 'Accept: application/vnd.github+json' \
        --header 'User-Agent: clicklang-installer' \
        "https://api.github.com/repos/$repository/releases/latest") \
        || fail 'could not look up the latest Click release'
    version=$(printf '%s\n' "$metadata" \
        | sed -n 's/.*"tag_name"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' \
        | sed -n '1p')
    [ -n "$version" ] || fail 'GitHub did not return a latest release tag'
fi
case "$version" in v*) version=${version#v} ;; esac
case "$version" in
    ''|*[!A-Za-z0-9.+-]*|.*|*..*|*.) fail "invalid Click version: $version" ;;
esac

if [ -n "${CLICK_HOME:-}" ]; then
    click_home=$CLICK_HOME
else
    [ -n "${HOME:-}" ] || fail 'set HOME or CLICK_HOME to choose an install directory'
    click_home=$HOME/.click
fi
case "$click_home" in
    /*) ;;
    *) click_home=$(pwd)/$click_home ;;
esac

installer_file=$(mktemp "${TMPDIR:-/tmp}/clicklang-installer.XXXXXX") \
    || fail 'could not create a temporary installer file'
trap 'rm -f "$installer_file"' 0
installer_url="https://github.com/$repository/releases/download/v$version/clicklang-installer.sh"

printf 'Installing Click %s from %s...\n' "$version" "$repository"
curl --fail --location --silent --show-error \
    --proto '=https' --tlsv1.2 --connect-timeout 15 --max-time 600 \
    --output "$installer_file" "$installer_url" \
    || fail "could not download the Click $version installer"

CLICKLANG_INSTALL_DIR=$click_home/bin \
CLICK_INSTALL_DIR=$click_home/bin \
CLICK_HOME=$click_home \
sh "$installer_file"

launcher=$click_home/bin/click
[ -x "$launcher" ] || fail "the release installer did not place click at $launcher"
CLICK_HOME=$click_home "$launcher" install "$version"
CLICK_HOME=$click_home "$launcher" default "$version"
printf 'Click %s is ready. Restart your shell if click is not on PATH yet.\n' "$version"
