#!/usr/bin/env bash
# tauceti-cache-get.sh — fetch TauCeti's published oleans for the pinned dependency revision
# from TauCeti's public, anonymous artifact cache (see TauCeti's scripts/lake-cache-get.sh).
# Mathlib's oleans are NOT here; run `lake exe cache get` for those.  A miss is not fatal:
# `lake build` then compiles TauCeti from source (hours).
set -euo pipefail
cd "$(dirname "$0")/.."
CFG="${TMPDIR:-/tmp}/gsarith-lake-cache.toml"
cat > "$CFG" <<TOML
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "${PUBLIC_ARTIFACT_ENDPOINT:-https://cache.taucetiproject.org/artifacts}"
revisionEndpoint = "${PUBLIC_REVISION_ENDPOINT:-https://cache.taucetiproject.org/revisions}"
TOML
LAKE_CONFIG="$CFG" lake cache get --package=TauCeti --service=tauceti-public \
  --repo=TauCetiProject/TauCeti --max-revs="${LAKE_CACHE_MAX_REVS:-100}"
