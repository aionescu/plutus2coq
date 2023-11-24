From Coq Require Extraction.
From Coq Require ExtrHaskellBasic.
From Coq Require ExtrHaskellNatInteger.
From Coq Require ExtrHaskellZInteger.
From Coq Require ExtrHaskellString.

Extraction Language Haskell.
Unset Extraction Optimize.
Set Extraction KeepSingleton.

Require Import ZArith.BinInt.

Extract Inlined Constant Z.eqb => "(PlutusTx.Eq.==)".
Extract Inlined Constant Z.mul => "(PlutusTx.Numeric.*)".

Require MathBounty.
Extraction Library MathBounty.
