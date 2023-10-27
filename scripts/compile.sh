#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)

ROOT=$(git rev-parse --show-toplevel)
PLUTUS=$ROOT/plutus
HS_TO_COQ=$ROOT/hs-to-coq
OUTPUT=$ROOT/coq-output

MODULES=(
  $OUTPUT/PlutusTx_These.v
  $OUTPUT/PlutusTx_Bool.v
  $OUTPUT/PlutusTx_Integer.v
  $OUTPUT/PlutusTx_Base.v
  $OUTPUT/PlutusTx_Either.v
  $OUTPUT/PlutusTx_Functor.v
  $OUTPUT/PlutusTx_Eq.v
  $OUTPUT/PlutusTx_Ord.v
  $OUTPUT/PlutusTx_ErrorCodes.v
  $OUTPUT/PlutusTx_Trace.v
  $OUTPUT/PlutusTx_List.v
  $OUTPUT/PlutusTx_Maybe.v
  $OUTPUT/PlutusTx_Semigroup.v
  $OUTPUT/PlutusTx_Monoid.v
  $OUTPUT/PlutusTx_Numeric.v
  $OUTPUT/PlutusTx_Applicative.v
  $OUTPUT/PlutusTx_Foldable.v
  $OUTPUT/PlutusTx_Traversable.v
  $OUTPUT/PlutusTx_Enum.v
  $OUTPUT/PlutusTx_Lattice.v
  $OUTPUT/PlutusTx_Ratio.v
  $OUTPUT/PlutusTx_Prelude.v
  $OUTPUT/PlutusTx_Sqrt.v
  $OUTPUT/PlutusTx_AssocMap.v
)

modcount=${#MODULES[@]}
i=0

for module in ${MODULES[@]}; do
  i=$((i+1))

  if [ -n "${1:-}" ] && [ "$1" -gt "$i" ]; then
    continue
  fi

  echo "[$i / $modcount] Compiling module $module..."

  coqc \
    -Q $HS_TO_COQ/base "" \
    -Q $HS_TO_COQ/base-thy "Proofs" \
    -Q $OUTPUT "" \
    $module
done
