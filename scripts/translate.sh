#!/usr/bin/env bash
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
PLUTUS=$ROOT/plutus
HS_TO_COQ=$ROOT/hs-to-coq
OUTPUT=$ROOT/coq-output

EXTENSIONS=(
  --ghc -XDeriveFoldable
  --ghc -XDeriveFunctor
  --ghc -XDeriveGeneric
  --ghc -XDeriveLift
  --ghc -XDeriveTraversable
  --ghc -XExplicitForAll
  --ghc -XGeneralizedNewtypeDeriving
  --ghc -XImportQualifiedPost
  --ghc -XScopedTypeVariables
  --ghc -XStandaloneDeriving
  --ghc -XDerivingStrategies
  --ghc -XDerivingVia
  --ghc -XFlexibleInstances
  --ghc -XFlexibleContexts
  --ghc -XDeriveDataTypeable
  --ghc -XBangPatterns
  --ghc -XTypeFamilies
  --ghc -XLambdaCase
)

IMPORTS=(
  --import-dir $PLUTUS/plutus-core/prelude
  --import-dir $PLUTUS/plutus-core/satint/src
  --import-dir $PLUTUS/plutus-core/plutus-core/src
  --import-dir $PLUTUS/plutus-core/plutus-core/stdlib
  --import-dir $PLUTUS/plutus-core/plutus-ir/src
  --import-dir $PLUTUS/plutus-core/index-envs/src
  --import-dir $PLUTUS/plutus-core/untyped-plutus-core/src
  --import-dir $PLUTUS/plutus-tx/src
  --import-dir $PLUTUS/prettyprinter-configurable/src
)

# The modules to translate to Coq, sorted in dependency order.
MODULES=(
  # $PLUTUS/plutus-tx/src/PlutusTx/Coverage.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Utils.hs
  $PLUTUS/plutus-tx/src/PlutusTx/These.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Bool.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Integer.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Base.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Either.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Functor.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Builtins/Internal.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Builtins/Class.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Builtins.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Eq.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Ord.hs
  $PLUTUS/plutus-tx/src/PlutusTx/ErrorCodes.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Trace.hs
  $PLUTUS/plutus-tx/src/PlutusTx/List.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Maybe.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Semigroup.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Monoid.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Numeric.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Applicative.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Foldable.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Traversable.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Enum.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lattice.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Lift/Class.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Lift/THUtils.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Lift/TH.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Lift/Instances.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Code.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Lift.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/IsData/Class.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/IsData/TH.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/IsData/Instances.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/IsData.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Ratio.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/AsData.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Prelude.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Sqrt.hs
  $PLUTUS/plutus-tx/src/PlutusTx/AssocMap.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Show/TH.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Show.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/Plugin/Utils.hs
  # $PLUTUS/plutus-tx/src/PlutusTx/TH.hs
  # $PLUTUS/plutus-tx/src/PlutusTx.hs
)

[ -n "${1:-}" ] || rm -rf $OUTPUT
mkdir -p $OUTPUT

cp $ROOT/coq-edits/Extract.v $OUTPUT/Extract.v

modcount=${#MODULES[@]}
i=0

for module in ${MODULES[@]}; do
  i=$((i+1))

  if [ -n "${1:-}" ] && [ "$1" -gt "$i" ]; then
    continue
  fi

  echo "[$i / $modcount] Translating module $module..."

  stack exec --stack-yaml $HS_TO_COQ/stack.yaml hs-to-coq -- \
    --nonrecursive \
    --ghc -v1 \
    --ghc -fdefer-type-errors \
    --ghc -fno-safe-haskell \
    ${EXTENSIONS[@]} \
    -o $OUTPUT \
    --preamble $ROOT/coq-edits/Preamble.v \
    --edits $HS_TO_COQ/base/edits \
    --edits $ROOT/coq-edits/edits \
    --iface-dir $HS_TO_COQ/base \
    --iface-dir $OUTPUT \
    ${IMPORTS[@]} \
    $module
done

# Patch out infix declarations that Coq doesn't want to compile.
echo "Patching Infix declarations..."
sed --in-place --regexp-extended 's/^(Infix \"[\&\|\<\>\+-\*/\].*) \(at.*\./\1./g' \
  $OUTPUT/PlutusTx_Bool.v \
  $OUTPUT/PlutusTx_Ord.v \
  $OUTPUT/PlutusTx_List.v \
  $OUTPUT/PlutusTx_Numeric.v \
  $OUTPUT/PlutusTx_Lattice.v
