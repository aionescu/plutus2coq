(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

From Coq Require Extraction.
From Coq Require ExtrHaskellBasic.
From Coq Require ExtrHaskellNatInteger.
From Coq Require ExtrHaskellZInteger.
From Coq Require ExtrHaskellString.

Extraction Language Haskell.
Unset Extraction Optimize.
Set Extraction KeepSingleton.

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted imports: *)

Require BinNums.
Require GHC.Base.
Require PlutusTx_AssocMap.
Require PlutusTx_Builtins_Internal.
Require PlutusTx_Eq.
Require PlutusTx_Lattice.
Require PlutusTx_Monoid.
Require PlutusTx_Numeric.
Require PlutusTx_Ord.
Require PlutusTx_Semigroup.
Require PlutusTx_These.
Require String.

(* Converted type declarations: *)

Inductive TokenName : Type :=
  | MkTokenName (unTokenName : PlutusTx_Builtins_Internal.BuiltinByteString)
   : TokenName.

Inductive MatchResult k v : Type :=
  | MatchSuccess : MatchResult k v
  | MatchPartial
   : list (v * v)%type ->
     list (k * v)%type -> list (k * v)%type -> MatchResult k v
  | MatchFailure : MatchResult k v.

Inductive CurrencySymbol : Type :=
  | MkCurrencySymbol (unCurrencySymbol
    : PlutusTx_Builtins_Internal.BuiltinByteString)
   : CurrencySymbol.

Inductive Value : Type :=
  | MkValue (getValue
    : PlutusTx_AssocMap.Map CurrencySymbol (PlutusTx_AssocMap.Map TokenName
                                            BinNums.Z))
   : Value.

Inductive AssetClass : Type :=
  | MkAssetClass (unAssetClass : (CurrencySymbol * TokenName)%type) : AssetClass.

Arguments MatchSuccess {_} {_}.

Arguments MatchPartial {_} {_} _ _ _.

Arguments MatchFailure {_} {_}.

Definition unTokenName (arg_0__ : TokenName) :=
  let 'MkTokenName unTokenName := arg_0__ in
  unTokenName.

Definition unCurrencySymbol (arg_0__ : CurrencySymbol) :=
  let 'MkCurrencySymbol unCurrencySymbol := arg_0__ in
  unCurrencySymbol.

Definition getValue (arg_0__ : Value) :=
  let 'MkValue getValue := arg_0__ in
  getValue.

Definition unAssetClass (arg_0__ : AssetClass) :=
  let 'MkAssetClass unAssetClass := arg_0__ in
  unAssetClass.

(* Converted value declarations: *)

Instance AdditiveSemigroup__Value : PlutusTx_Numeric.AdditiveSemigroup Value.
Proof.
Admitted.

Instance AdditiveMonoid__Value : PlutusTx_Numeric.AdditiveMonoid Value.
Proof.
Admitted.

Instance AdditiveGroup__Value : PlutusTx_Numeric.AdditiveGroup Value.
Proof.
Admitted.

(* Skipping all instances of class `Data.String.IsString', including
   `PlutusLedgerApi_V1_Value.IsString__TokenName' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusLedgerApi_V1_Value.Show__TokenName' *)

Instance Eq___Value : GHC.Base.Eq_ Value.
Proof.
Admitted.

Instance Eq__Value : PlutusTx_Eq.Eq Value.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Semigroup', including
   `PlutusLedgerApi_V1_Value.Semigroup__Value' *)

Instance Semigroup__Value : PlutusTx_Semigroup.Semigroup Value.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Monoid', including
   `PlutusLedgerApi_V1_Value.Monoid__Value' *)

Instance Monoid__Value : PlutusTx_Monoid.Monoid Value.
Proof.
Admitted.

Instance Group__Value : PlutusTx_Monoid.Group Value.
Proof.
Admitted.

(* Skipping all instances of class `PlutusTx_Numeric.Module', including
   `PlutusLedgerApi_V1_Value.Module__Z__Value' *)

Instance JoinSemiLattice__Value : PlutusTx_Lattice.JoinSemiLattice Value.
Proof.
Admitted.

Instance MeetSemiLattice__Value : PlutusTx_Lattice.MeetSemiLattice Value.
Proof.
Admitted.

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Value.Lift__DefaultUni__CurrencySymbol' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Value.Typeable__DefaultUni__CurrencySymbol' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Value.Lift__DefaultUni__TokenName' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Value.Typeable__DefaultUni__TokenName' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Value.Lift__DefaultUni__AssetClass' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Value.Typeable__DefaultUni__AssetClass' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Value.Lift__DefaultUni__Value' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Value.Typeable__DefaultUni__Value' *)

Axiom currencySymbol : String.string -> CurrencySymbol.

Axiom tokenName : String.string -> TokenName.

Axiom fromText : String.string -> TokenName.

Axiom fromTokenName : forall {r},
                      (String.string -> r) -> (String.string -> r) -> TokenName -> r.

Axiom asBase16 : String.string -> String.string.

Axiom quoted : String.string -> String.string.

Axiom toString : TokenName -> GHC.Base.String.

Axiom adaSymbol : CurrencySymbol.

Axiom adaToken : TokenName.

Axiom assetClass : CurrencySymbol -> TokenName -> AssetClass.

Axiom valueOf : Value -> CurrencySymbol -> TokenName -> BinNums.Z.

Axiom symbols : Value -> list CurrencySymbol.

Axiom singleton : CurrencySymbol -> TokenName -> BinNums.Z -> Value.

Axiom assetClassValue : AssetClass -> BinNums.Z -> Value.

Axiom assetClassValueOf : Value -> AssetClass -> BinNums.Z.

Axiom unionVal : Value ->
                 Value ->
                 PlutusTx_AssocMap.Map CurrencySymbol (PlutusTx_AssocMap.Map TokenName
                                                       (PlutusTx_These.These BinNums.Z BinNums.Z)).

Axiom unionWith : (BinNums.Z -> BinNums.Z -> BinNums.Z) ->
                  Value -> Value -> Value.

Axiom flattenValue : Value ->
                     list (CurrencySymbol * TokenName * BinNums.Z)%type.

Axiom isZero : Value -> bool.

Axiom checkPred : (PlutusTx_These.These BinNums.Z BinNums.Z -> bool) ->
                  Value -> Value -> bool.

Axiom checkBinRel : (BinNums.Z -> BinNums.Z -> bool) -> Value -> Value -> bool.

Axiom geq : Value -> Value -> bool.

Axiom leq : Value -> Value -> bool.

Axiom gt : Value -> Value -> bool.

Axiom lt : Value -> Value -> bool.

Axiom split : Value -> (Value * Value)%type.

Axiom unsafeInsertUnique : forall {k} {v},
                           forall `{PlutusTx_Ord.Ord k}, k -> v -> list (k * v)%type -> list (k * v)%type.

Axiom unsafeInsertionSortUnique : forall {k} {v},
                                  forall `{PlutusTx_Ord.Ord k}, list (k * v)%type -> list (k * v)%type.

Axiom matchKVs : forall {k} {v},
                 forall `{PlutusTx_Ord.Ord k},
                 (v -> bool) ->
                 (v -> v -> bool) -> list (k * v)%type -> list (k * v)%type -> MatchResult k v.

Axiom eqKVs : forall {k} {v},
              forall `{PlutusTx_Eq.Eq k},
              (v -> bool) ->
              (v -> v -> bool) -> list (k * v)%type -> list (k * v)%type -> bool.

Axiom eq : Value -> Value -> bool.

(* External variables:
     bool list op_zt__ BinNums.Z GHC.Base.Eq_ GHC.Base.String PlutusTx_AssocMap.Map
     PlutusTx_Builtins_Internal.BuiltinByteString PlutusTx_Eq.Eq
     PlutusTx_Lattice.JoinSemiLattice PlutusTx_Lattice.MeetSemiLattice
     PlutusTx_Monoid.Group PlutusTx_Monoid.Monoid PlutusTx_Numeric.AdditiveGroup
     PlutusTx_Numeric.AdditiveMonoid PlutusTx_Numeric.AdditiveSemigroup
     PlutusTx_Ord.Ord PlutusTx_Semigroup.Semigroup PlutusTx_These.These String.string
*)
