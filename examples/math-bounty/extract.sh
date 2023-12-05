#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
HS_TO_COQ=$ROOT/hs-to-coq
PLUTUS_COQ=$ROOT/plutus-coq
SRC_COQ=$ROOT/examples/math-bounty/src-coq
SRC_HS=$ROOT/examples/math-bounty/src-hs

MODULES=(
  $SRC_COQ/MathBounty.v
  $SRC_COQ/ExtractionWrapper.v
)

cd $SRC_HS

num_modules=${#MODULES[@]}
i=0

for module in ${MODULES[@]}; do
  i=$((i+1))
  echo "[$i / $num_modules] Compiling $module"

  coqc \
    -Q $HS_TO_COQ/base "" \
    -Q $HS_TO_COQ/base-thy "Proofs" \
    -Q $PLUTUS_COQ "" \
    -Q $SRC_COQ "" \
    $module
done
