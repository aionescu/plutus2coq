module MathBountyFixed where

import qualified Prelude
import qualified PlutusLedgerApi.V3.Contexts

import PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Show qualified as PlutusTx

data Datum =
   MkDatum Prelude.Integer

PlutusTx.unstableMakeIsData ''Datum

square :: Datum -> Prelude.Integer
square d =
  case d of {
   MkDatum square0 -> square0}
{-# INLINEABLE square #-}

data Redeemer =
   MkRedeemer Prelude.Integer

PlutusTx.unstableMakeIsData ''Redeemer

guess :: Redeemer -> Prelude.Integer
guess r =
  case r of {
   MkRedeemer guess0 -> guess0}
{-# INLINEABLE guess #-}

mathBounty :: Datum -> Redeemer -> PlutusLedgerApi.V3.Contexts.ScriptContext
              -> Prelude.Bool
mathBounty datum redeemer _ =
  (Prelude.==) ((Prelude.*) (guess redeemer) (guess redeemer)) (square datum)
{-# INLINEABLE mathBounty #-}

mathBountyUntypedValidator :: BuiltinData -> BuiltinData -> BuiltinData -> ()
mathBountyUntypedValidator datum redeemer ctx =
  PlutusTx.check
  ( mathBounty
    (PlutusTx.unsafeFromBuiltinData datum)
    (PlutusTx.unsafeFromBuiltinData redeemer)
    (PlutusTx.unsafeFromBuiltinData ctx)
  )
{-# INLINEABLE mathBountyUntypedValidator #-}

mathBountyValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
mathBountyValidatorScript = $$(PlutusTx.compile [|| mathBountyUntypedValidator ||])
