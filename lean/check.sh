#!/usr/bin/env bash
# Reproduce the Lean check of the proof of `divergence_for_p_lt_half`
# (formal-conjectures pull request 3675, FormalConjectures/Arxiv/1905.10899/LastIterateConvergence.lean).
# Usage: bash check.sh /path/to/formal-conjectures
#   Tested with a formal-conjectures checkout at commit ab0addc45f699bdd0b7cc58efa5140a72f101a9e
#   (Lean v4.33.1); run `lake exe cache get` in the checkout first. All files import Mathlib only
#   (plus each other). Defs.lean is a verbatim copy of the definitions of the pull-request file
#   (see ../scripts/check_verbatim.py, which compares against lean/reference/).
set -euo pipefail
FC="$(cd "$1" && pwd)"
HERE="$(cd "$(dirname "$0")" && pwd)"
D=DMSolutions/LastIterate
mkdir -p "$FC/$D"
cp "$HERE"/$D/*.lean "$FC/$D/"
cd "$FC"
O=.lake/build/lib/lean
mkdir -p "$O/$D"
echo "== formal-conjectures commit: $(git rev-parse HEAD)"
for f in Uniqueness Defs Growth Analytic Dynamics Solution; do
  echo "== compiling $f.lean"
  lake env lean -o "$O/$D/$f.olean" $D/$f.lean
done
echo "== compiling CheckAnswer.lean (verbatim statement under its original name; type equality by rfl; axioms)"
lake env lean $D/CheckAnswer.lean
echo "== forbidden keywords (sorry/admit/native_decide/axiom):"
FILES=""
for f in Uniqueness Defs Growth Analytic Dynamics Solution CheckAnswer; do FILES="$FILES $D/$f.lean"; done
grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' $FILES || echo "none"
echo "== done"
