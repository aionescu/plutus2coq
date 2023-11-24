module MathBountyFixed where

import qualified Prelude
import qualified PlutusLedgerApi.V1.Interval
import qualified PlutusLedgerApi.V1.Time
import qualified PlutusLedgerApi.V3.Contexts
import qualified PlutusTx.Functor
import qualified PlutusTx.Eq
import qualified PlutusTx.Numeric

import PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx

data Datum =
  MkDatum Prelude.Integer PlutusLedgerApi.V1.Time.POSIXTime

PlutusTx.unstableMakeIsData ''Datum

{-# INLINEABLE square #-}
square :: Datum -> Prelude.Integer
square d =
  case d of
    MkDatum square0 _ -> square0

{-# INLINEABLE deadline #-}
deadline :: Datum -> PlutusLedgerApi.V1.Time.POSIXTime
deadline d =
  case d of
    MkDatum _ deadline0 -> deadline0

data Redeemer =
  MkRedeemer Prelude.Integer

PlutusTx.unstableMakeIsData ''Redeemer

{-# INLINEABLE guess #-}
guess :: Redeemer -> Prelude.Integer
guess r =
  case r of
    MkRedeemer guess0 -> guess0

{-# INLINEABLE mathBounty #-}
mathBounty :: Datum -> Redeemer -> PlutusLedgerApi.V3.Contexts.ScriptContext -> Prelude.Bool
mathBounty datum redeemer ctx =
  let
    guessCorrect =
      let guess0 = guess redeemer in
        (PlutusTx.Eq.==) ((PlutusTx.Numeric.*) guess0 guess0) (square datum)

    beforeDeadline =
      let
        deadlineRange =
          PlutusLedgerApi.V1.Interval.to (PlutusLedgerApi.V1.Time.getPOSIXTime (deadline datum))

        txRange =
          PlutusTx.Functor.fmap PlutusLedgerApi.V1.Time.getPOSIXTime
            (PlutusLedgerApi.V3.Contexts.txInfoValidRange (PlutusLedgerApi.V3.Contexts.scriptContextTxInfo ctx))
      in
      PlutusLedgerApi.V1.Interval.contains deadlineRange txRange
  in
  (Prelude.&&) guessCorrect beforeDeadline

{-# INLINEABLE mathBountyUntypedValidator #-}
mathBountyUntypedValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mathBountyUntypedValidator datum redeemer ctx =
  PlutusTx.check
  ( mathBounty
    (PlutusTx.unsafeFromBuiltinData datum)
    (PlutusTx.unsafeFromBuiltinData redeemer)
    (PlutusTx.unsafeFromBuiltinData ctx)
  )

mathBountyValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
mathBountyValidatorScript = $$(PlutusTx.compile [|| mathBountyUntypedValidator ||])
