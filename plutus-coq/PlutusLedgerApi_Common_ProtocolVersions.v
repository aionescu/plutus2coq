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

Require GHC.Base.
Require GHC.Enum.
Require GHC.Num.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive MajorProtocolVersion : Type :=
  | MkMajorProtocolVersion (getMajorProtocolVersion : GHC.Num.Int)
   : MajorProtocolVersion.

Definition getMajorProtocolVersion (arg_0__ : MajorProtocolVersion) :=
  let 'MkMajorProtocolVersion getMajorProtocolVersion := arg_0__ in
  getMajorProtocolVersion.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_Common_ProtocolVersions.Pretty__MajorProtocolVersion' *)

Definition shelleyPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #2.

Definition allegraPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #3.

Definition maryPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #4.

Definition alonzoPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #5.

Definition vasilPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #7.

Definition valentinePV : MajorProtocolVersion :=
  MkMajorProtocolVersion #8.

Definition conwayPV : MajorProtocolVersion :=
  MkMajorProtocolVersion #9.

Definition knownPVs : list MajorProtocolVersion :=
  GHC.Base.id (cons shelleyPV (cons allegraPV (cons maryPV (cons alonzoPV (cons
                                                                  vasilPV (cons valentinePV (cons conwayPV nil))))))).

Definition futurePV : MajorProtocolVersion :=
  MkMajorProtocolVersion GHC.Enum.maxBound.

(* External variables:
     cons list nil GHC.Base.id GHC.Enum.maxBound GHC.Num.Int GHC.Num.fromInteger
*)
