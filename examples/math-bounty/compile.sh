#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
HS_TO_COQ=$ROOT/hs-to-coq
PLUTUS_COQ=$ROOT/plutus-coq
SRC_COQ=$ROOT/examples/math-bounty/src-coq
SRC_HS=$ROOT/examples/math-bounty/src-hs

cd $SRC_HS

coqc \
  -Q $HS_TO_COQ/base "" \
  -Q $HS_TO_COQ/base-thy "Proofs" \
  -Q $PLUTUS_COQ "" \
  -Q $SRC_COQ "" \
  $SRC_COQ/MathBounty.v $SRC_COQ/ExtractionWrapper.v
