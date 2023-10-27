#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)

ROOT=$(git rev-parse --show-toplevel)
PLUTUS=$ROOT/plutus
HS_TO_COQ=$ROOT/hs-to-coq
OUTPUT=$ROOT/coq-output
EXTRACTED=$ROOT/coq-extracted/src

rm -rf $EXTRACTED
mkdir -p $EXTRACTED
cd $EXTRACTED

coqc \
  -Q $ROOT/coq-output "" \
  -Q $HS_TO_COQ/base "" \
  -Q $HS_TO_COQ/base-thy "Proofs" \
  $ROOT/coq-output/Extract.v

IMPORTS="import qualified Prelude\\nimport qualified Data.Bits\\nimport qualified Data.Char"

echo "Fixing up Haskell imports..."
sed -Ei "s/import qualified Prelude/$IMPORTS/g" $EXTRACTED/*.hs
