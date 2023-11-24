#!/usr/bin/env bash
set -euo pipefail

# This script translates PlutusTx and related modules to Coq using hs-to-coq.

# Specify all dirs relative to repo root, to allow running the script anywhere within the repo.
ROOT=$(git rev-parse --show-toplevel)
PLUTUS=$ROOT/plutus
HS_TO_COQ=$ROOT/hs-to-coq
EDITS=$ROOT/edits
PLUTUS_COQ=$ROOT/plutus-coq

# GHC extensions to enable when translating to Coq.
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
  --ghc -XMultiParamTypeClasses
)

# Directories to search for Haskell imports.
IMPORTS=(
  --import-dir $PLUTUS/plutus-core/prelude
  --import-dir $PLUTUS/plutus-core/satint/src
  --import-dir $PLUTUS/plutus-core/plutus-core/src
  --import-dir $PLUTUS/plutus-core/plutus-core/stdlib
  --import-dir $PLUTUS/plutus-core/plutus-ir/src
  --import-dir $PLUTUS/plutus-core/index-envs/src
  --import-dir $PLUTUS/plutus-core/untyped-plutus-core/src
  --import-dir $PLUTUS/plutus-tx/src
  --import-dir $PLUTUS/plutus-ledger-api/src
  --import-dir $PLUTUS/prettyprinter-configurable/src
)

# The modules to translate to Coq, sorted in dependency order.
MODULES=(
  $PLUTUS/plutus-core/plutus-core/src/PlutusCore/Data.hs
  $PLUTUS/plutus-core/plutus-core/src/PlutusCore/Evaluation/Result.hs
  $PLUTUS/plutus-core/plutus-core/src/PlutusCore/Builtin/Emitter.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Utils.hs
  $PLUTUS/plutus-tx/src/PlutusTx/These.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Bool.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Integer.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Base.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Either.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Functor.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Builtins/Internal.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Builtins/Class.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Builtins.hs
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
  $PLUTUS/plutus-tx/src/PlutusTx/Code.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Plugin/Utils.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lift/Class.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lift/THUtils.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lift/TH.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lift/Instances.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Lift.hs
  $PLUTUS/plutus-tx/src/PlutusTx/IsData/Class.hs
  $PLUTUS/plutus-tx/src/PlutusTx/IsData/TH.hs
  $PLUTUS/plutus-tx/src/PlutusTx/IsData/Instances.hs
  $PLUTUS/plutus-tx/src/PlutusTx/IsData.hs
  $PLUTUS/plutus-tx/src/PlutusTx/AsData.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Ratio.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Prelude.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Sqrt.hs
  $PLUTUS/plutus-tx/src/PlutusTx/AssocMap.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Coverage.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Show/TH.hs
  $PLUTUS/plutus-tx/src/PlutusTx/Show.hs
  $PLUTUS/plutus-tx/src/PlutusTx/TH.hs
  $PLUTUS/plutus-tx/src/PlutusTx.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/Common/ParamName.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/Common/ProtocolVersions.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/Common/Versions.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/Common.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Crypto.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Scripts.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Credential.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Address.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Bytes.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Value.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Tx.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/DCert.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Interval.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Time.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/Contexts.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/EvaluationContext.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1/ParamName.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V1.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V2/Tx.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V2/Contexts.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V2/EvaluationContext.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V2/ParamName.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V2.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V3/Contexts.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V3/EvaluationContext.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V3/ParamName.hs
  $PLUTUS/plutus-ledger-api/src/PlutusLedgerApi/V3.hs
)

# Clean output dir first, for more reproducible results.
rm -rf $PLUTUS_COQ
mkdir -p $PLUTUS_COQ

num_steps=$((${#MODULES[@]} + 1))
i=0

# Main loop, calls hs-to-coq on every module in $MODULES.
for module in ${MODULES[@]}; do
  i=$((i+1))
  echo "[$i / $num_steps] Translating $module"

  stack exec --stack-yaml $HS_TO_COQ/stack.yaml hs-to-coq -- \
    --nonrecursive \
    ${EXTENSIONS[@]} \
    -o $PLUTUS_COQ \
    --preamble $EDITS/Preamble.v \
    --edits $HS_TO_COQ/base/edits \
    --edits $EDITS/edits \
    --iface-dir $HS_TO_COQ/base \
    --iface-dir $PLUTUS_COQ \
    ${IMPORTS[@]} \
    $module
done

# Patch out some infix declarations that specify incorrect precedence level.
echo "[$num_steps / $num_steps] Patching Infix declarations."
sed --in-place --regexp-extended 's/^(Infix \"[\&\|\<\>\+-\*/\].*) \(at.*\./\1./g' \
  $PLUTUS_COQ/PlutusTx_Bool.v \
  $PLUTUS_COQ/PlutusTx_Ord.v \
  $PLUTUS_COQ/PlutusTx_List.v \
  $PLUTUS_COQ/PlutusTx_Numeric.v \
  $PLUTUS_COQ/PlutusTx_Lattice.v
