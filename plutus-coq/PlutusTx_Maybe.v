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

Require PlutusTx_Base.
Require PlutusTx_List.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition isJust {a : Type} : option a -> bool :=
  fun m => match m with | Some _ => true | _ => false end.

Definition isNothing {a : Type} : option a -> bool :=
  fun m => match m with | Some _ => false | _ => true end.

Definition maybe {b : Type} {a : Type} : b -> (a -> b) -> option a -> b :=
  fun b f m => match m with | None => b | Some a => f a end.

Definition fromMaybe {a : Type} : a -> option a -> a :=
  fun a => maybe a PlutusTx_Base.id.

Definition mapMaybe {a : Type} {b : Type}
   : (a -> option b) -> list a -> list b :=
  fun p =>
    PlutusTx_List.foldr (fun e xs =>
                           maybe xs (fun arg_0__ => cons arg_0__ xs) (p e)) nil.

(* External variables:
     None Some Type bool cons false list nil option true PlutusTx_Base.id
     PlutusTx_List.foldr
*)
