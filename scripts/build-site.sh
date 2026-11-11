#!/usr/bin/env bash
# Build the whole Click website into one directory: the guide (guide/, built
# by the VitePress project in site/) at the root, and the AI reference (docs/,
# built by mdBook) under reference/. The reference's llms.txt is also written
# at the root, where agents look for it, with its links pointing into
# reference/. .github/workflows/pages.yml deploys this directory.
#
# Usage: scripts/build-site.sh [DIR]      (default: target/click-pages)
#
# CLICK_SITE_BASE is the URL path the site is served under, with a trailing
# slash: `/` for a domain root (the default), `/click/` for a GitHub project
# site.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

output="${1:-$PWD/target/click-pages}"
base="${CLICK_SITE_BASE:-/}"
if [[ "$base" != /* || "$base" != */ ]]; then
    echo "build-site: CLICK_SITE_BASE must start and end with '/': $base" >&2
    exit 2
fi
export CLICK_SITE_BASE="$base"

# The reference. mdBook's links are relative; only its 404 page needs the
# path it is served under.
MDBOOK_OUTPUT__HTML__SITE_URL="${base}reference/" scripts/mdbook-build.sh
scripts/build-ai-reference.sh "$PWD/target/click-docs"

# The guide.
(
    cd site
    if [[ ! -d node_modules || package-lock.json -nt node_modules ]]; then
        npm ci
    fi
    npx vitepress build
)

rm -rf "$output"
mkdir -p "$output"
cp -R target/click-site/. "$output/"
cp -R target/click-docs "$output/reference"
sed -E 's#\]\(([^):]+)\)#](reference/\1)#g' target/click-docs/llms.txt > "$output/llms.txt"
# GitHub Pages runs Jekyll over a site without this file.
touch "$output/.nojekyll"

echo "build-site: wrote $output"
