module MathBounty where

import qualified Prelude
import qualified PlutusLedgerApi_V3_Contexts

data Datum =
   MkDatum Prelude.Integer

square :: Datum -> Prelude.Integer
square d =
  case d of {
   MkDatum square0 -> square0}

data Redeemer =
   MkRedeemer Prelude.Integer

guess :: Redeemer -> Prelude.Integer
guess r =
  case r of {
   MkRedeemer guess0 -> guess0}

mathBounty :: Datum -> Redeemer -> PlutusLedgerApi_V3_Contexts.ScriptContext
              -> Prelude.Bool
mathBounty datum redeemer _ =
  (Prelude.==) ((Prelude.*) (guess redeemer) (guess redeemer)) (square datum)

