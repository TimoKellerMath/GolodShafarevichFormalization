#!/usr/bin/env bash
# check_axioms.sh — build the library and run the axiom audit (scripts/Axioms.lean).
#
# The audit fails if any GSArith declaration uses an axiom outside
# {propext, Classical.choice, Quot.sound, sorryAx}  (home-rolled axioms, native_decide, …),
# or if any @[gs_public] declaration depends on sorryAx.  Every sorryAx user is listed, so the
# output can be cross-checked against LEDGER.md.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake build axioms
lake exe axioms
