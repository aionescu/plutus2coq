{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module MathBounty where

import qualified Prelude
import qualified PlutusLedgerApi_V1_Interval
import qualified PlutusLedgerApi_V1_Time
import qualified PlutusLedgerApi_V3_Contexts
import qualified PlutusTx_Enum
import qualified PlutusTx_Eq
import qualified PlutusTx_Functor
import qualified PlutusTx_Ord

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

data Datum =
   MkDatum Prelude.Integer PlutusLedgerApi_V1_Time.POSIXTime

square :: Datum -> Prelude.Integer
square d =
  case d of {
   MkDatum square0 _ -> square0}

deadline :: Datum -> PlutusLedgerApi_V1_Time.POSIXTime
deadline d =
  case d of {
   MkDatum _ deadline0 -> deadline0}

data Redeemer =
   MkRedeemer Prelude.Integer

guess :: Redeemer -> Prelude.Integer
guess r =
  case r of {
   MkRedeemer guess0 -> guess0}

mathBounty :: Datum -> Redeemer -> PlutusLedgerApi_V3_Contexts.ScriptContext
              -> Prelude.Bool
mathBounty datum redeemer ctx =
  let {
   guessCorrect = let {guess0 = guess redeemer} in
                  (PlutusTx.Eq.==) ((PlutusTx.Numeric.*) guess0 guess0)
                    (square datum)}
  in
  let {
   beforeDeadline = let {
                     deadlineRange = PlutusLedgerApi_V1_Interval.to
                                       (PlutusLedgerApi_V1_Time.getPOSIXTime
                                         (deadline datum))}
                    in
                    let {
                     txRange = PlutusTx_Functor.fmap
                                 (unsafeCoerce (\_ ->
                                   PlutusLedgerApi_V1_Interval.coq_Functor__Interval))
                                 PlutusLedgerApi_V1_Time.getPOSIXTime
                                 (PlutusLedgerApi_V3_Contexts.txInfoValidRange
                                   (PlutusLedgerApi_V3_Contexts.scriptContextTxInfo
                                     ctx))}
                    in
                    PlutusLedgerApi_V1_Interval.contains
                      (unsafeCoerce (\_ -> PlutusTx_Enum.coq_Enum__Z))
                      (unsafeCoerce (\_ -> PlutusTx_Eq.coq_Eq__Z))
                      (unsafeCoerce (\_ -> PlutusTx_Ord.coq_Ord__Z))
                      (unsafeCoerce deadlineRange) txRange}
  in
  (Prelude.&&) guessCorrect beforeDeadline

