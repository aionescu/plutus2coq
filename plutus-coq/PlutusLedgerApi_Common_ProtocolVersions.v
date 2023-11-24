(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted imports: *)

Require Data.Set.Internal.
Require GHC.Enum.
Require GHC.Num.
Require HsToCoq.Err.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive MajorProtocolVersion : Type :=
  | MajorProtocolVersion (getMajorProtocolVersion : GHC.Num.Int)
   : MajorProtocolVersion.

Instance Default__MajorProtocolVersion
   : HsToCoq.Err.Default MajorProtocolVersion :=
  HsToCoq.Err.Build_Default _ (MajorProtocolVersion HsToCoq.Err.default).

Definition getMajorProtocolVersion (arg_0__ : MajorProtocolVersion) :=
  let 'MajorProtocolVersion getMajorProtocolVersion := arg_0__ in
  getMajorProtocolVersion.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_Common_ProtocolVersions.Pretty__MajorProtocolVersion' *)

Definition shelleyPV : MajorProtocolVersion :=
  MajorProtocolVersion #2.

Definition allegraPV : MajorProtocolVersion :=
  MajorProtocolVersion #3.

Definition maryPV : MajorProtocolVersion :=
  MajorProtocolVersion #4.

Definition alonzoPV : MajorProtocolVersion :=
  MajorProtocolVersion #5.

Definition vasilPV : MajorProtocolVersion :=
  MajorProtocolVersion #7.

Definition valentinePV : MajorProtocolVersion :=
  MajorProtocolVersion #8.

Definition conwayPV : MajorProtocolVersion :=
  MajorProtocolVersion #9.

Definition knownPVs : Data.Set.Internal.Set_ MajorProtocolVersion :=
  Data.Set.Internal.fromList (cons shelleyPV (cons allegraPV (cons maryPV (cons
                                                                    alonzoPV (cons vasilPV (cons valentinePV (cons
                                                                                                  conwayPV nil))))))).

Definition futurePV : MajorProtocolVersion :=
  MajorProtocolVersion GHC.Enum.maxBound.

(* External variables:
     cons nil Data.Set.Internal.Set_ Data.Set.Internal.fromList GHC.Enum.maxBound
     GHC.Num.Int GHC.Num.fromInteger HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default
*)
