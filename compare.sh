#!/usr/bin/env bash
#
# Check a solution against a challenge with comparator.
# Run from the root of this Lean project.

set -euo pipefail

# --- FILL ME -----------------------------------------------------------------

COMPARATOR="$HOME/comparator/.lake/build/bin/comparator"
LEAN4EXPORT_DIR="$HOME/comparator/.lake/packages/lean4export/.lake/build/bin"

export COMPARATOR_LANDRUN="$HOME/landrun"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT_DIR/lean4export"

export PATH="$HOME:$LEAN4EXPORT_DIR:$PATH"


# Module name, i.e. Challenge/$NAME.lean and Solution/$NAME.lean.
NAME=VonNeumannDoubleCommutantTheorem

# Files to copy in. Leave a path empty to use whatever is already in place.
CHALLENGE_SRC=/home/rachelteo_sakana_ai/FormalQualBench-Challenge/FormalQualBench/$NAME/Main.lean
SOLUTION_SRC=./FormalQualBench/$NAME/Main.lean

# Theorems comparator must check.
THEOREMS=(
  "$NAME.MainTheorem"
)

# -----------------------------------------------------------------------------

[[ -n "$CHALLENGE_SRC" ]] && cp "$CHALLENGE_SRC" "Challenge/$NAME.lean"
[[ -n "$SOLUTION_SRC"  ]] && cp "$SOLUTION_SRC"  "Solution/$NAME.lean"

echo "import Challenge.$NAME" > Challenge.lean
echo "import Solution.$NAME"  > Solution.lean

theorem_json=$(printf '"%s",' "${THEOREMS[@]}")
cat > config.json <<EOF
{
  "challenge_module": "Challenge.$NAME",
  "solution_module": "Solution.$NAME",
  "theorem_names": [${theorem_json%,}],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
EOF

lake env "$COMPARATOR" config.json
