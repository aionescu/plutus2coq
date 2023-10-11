(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require FastString.
Require GHC.Base.
Require Name.
Require Pair.
Require SrcLoc.
Require Unique.

(* Converted type declarations: *)

Definition TypeEqn :=
  (Pair.Pair AxiomatizedTypes.Type_)%type.

Axiom Branches : AxiomatizedTypes.BranchFlag -> Type.

(* Converted value declarations: *)

Instance Eq___Role : GHC.Base.Eq_ AxiomatizedTypes.Role.
Proof.
Admitted.

Instance Ord__Role : GHC.Base.Ord AxiomatizedTypes.Role.
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__Role' *)

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxBranch' *)

Instance Eq___CoAxiom : forall {br}, GHC.Base.Eq_ (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

Instance Uniquable__CoAxiom
   : forall {br}, Unique.Uniquable (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiom' *)

Instance NamedThing__CoAxiom
   : forall {br}, Name.NamedThing (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxiom' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxBranch' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__Role' *)

(* Skipping all instances of class `Binary.Binary', including
   `CoAxiom.Binary__Role' *)

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxiomRule' *)

Instance Uniquable__CoAxiomRule : Unique.Uniquable AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

Instance Eq___CoAxiomRule : GHC.Base.Eq_ AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

Instance Ord__CoAxiomRule : GHC.Base.Ord AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiomRule' *)

Axiom manyBranches : list AxiomatizedTypes.CoAxBranch ->
                     Branches AxiomatizedTypes.Branched.

Axiom unbranched : AxiomatizedTypes.CoAxBranch ->
                   Branches AxiomatizedTypes.Unbranched.

Axiom toBranched : forall {br},
                   Branches br -> Branches AxiomatizedTypes.Branched.

Axiom toUnbranched : forall {br},
                     Branches br -> Branches AxiomatizedTypes.Unbranched.

Axiom fromBranches : forall {br : AxiomatizedTypes.BranchFlag},
                     Branches br -> list AxiomatizedTypes.CoAxBranch.

Axiom branchesNth : forall {br},
                    Branches br -> AxiomatizedTypes.BranchIndex -> AxiomatizedTypes.CoAxBranch.

Axiom numBranches : forall {br : AxiomatizedTypes.BranchFlag},
                    Branches br -> nat.

Axiom mapAccumBranches : forall {br : AxiomatizedTypes.BranchFlag},
                         (list AxiomatizedTypes.CoAxBranch ->
                          AxiomatizedTypes.CoAxBranch -> AxiomatizedTypes.CoAxBranch) ->
                         Branches br -> Branches br.

Axiom toBranchedAxiom : forall {br : AxiomatizedTypes.BranchFlag},
                        AxiomatizedTypes.CoAxiom br ->
                        AxiomatizedTypes.CoAxiom AxiomatizedTypes.Branched.

Axiom toUnbranchedAxiom : forall {br : AxiomatizedTypes.BranchFlag},
                          AxiomatizedTypes.CoAxiom br ->
                          AxiomatizedTypes.CoAxiom AxiomatizedTypes.Unbranched.

Axiom coAxiomNumPats : forall {br : AxiomatizedTypes.BranchFlag},
                       AxiomatizedTypes.CoAxiom br -> nat.

Axiom coAxiomNthBranch : forall {br : AxiomatizedTypes.BranchFlag},
                         AxiomatizedTypes.CoAxiom br ->
                         AxiomatizedTypes.BranchIndex -> AxiomatizedTypes.CoAxBranch.

Axiom coAxiomArity : forall {br : AxiomatizedTypes.BranchFlag},
                     AxiomatizedTypes.CoAxiom br -> AxiomatizedTypes.BranchIndex -> BasicTypes.Arity.

Axiom coAxiomName : forall {br : AxiomatizedTypes.BranchFlag},
                    AxiomatizedTypes.CoAxiom br -> Name.Name.

Axiom coAxiomRole : forall {br : AxiomatizedTypes.BranchFlag},
                    AxiomatizedTypes.CoAxiom br -> AxiomatizedTypes.Role.

Axiom coAxiomBranches : forall {br : AxiomatizedTypes.BranchFlag},
                        AxiomatizedTypes.CoAxiom br -> Branches br.

Axiom coAxiomSingleBranch_maybe : forall {br : AxiomatizedTypes.BranchFlag},
                                  AxiomatizedTypes.CoAxiom br -> option AxiomatizedTypes.CoAxBranch.

Axiom coAxiomSingleBranch : AxiomatizedTypes.CoAxiom
                            AxiomatizedTypes.Unbranched ->
                            AxiomatizedTypes.CoAxBranch.

Axiom coAxiomTyCon : forall {br : AxiomatizedTypes.BranchFlag},
                     AxiomatizedTypes.CoAxiom br -> Core.TyCon.

Axiom coAxBranchTyVars : AxiomatizedTypes.CoAxBranch -> list Core.TyVar.

Axiom coAxBranchCoVars : AxiomatizedTypes.CoAxBranch -> list Core.CoVar.

Axiom coAxBranchLHS : AxiomatizedTypes.CoAxBranch ->
                      list AxiomatizedTypes.Type_.

Axiom coAxBranchRHS : AxiomatizedTypes.CoAxBranch -> AxiomatizedTypes.Type_.

Axiom coAxBranchRoles : AxiomatizedTypes.CoAxBranch ->
                        list AxiomatizedTypes.Role.

Axiom coAxBranchSpan : AxiomatizedTypes.CoAxBranch -> SrcLoc.SrcSpan.

Axiom isImplicitCoAxiom : forall {br : AxiomatizedTypes.BranchFlag},
                          AxiomatizedTypes.CoAxiom br -> bool.

Axiom coAxBranchIncomps : AxiomatizedTypes.CoAxBranch ->
                          list AxiomatizedTypes.CoAxBranch.

Axiom placeHolderIncomps : list AxiomatizedTypes.CoAxBranch.

Axiom fsFromRole : AxiomatizedTypes.Role -> FastString.FastString.

Axiom trivialBuiltInFamily : AxiomatizedTypes.BuiltInSynFamily.

(* External variables:
     Type bool list nat option AxiomatizedTypes.BranchFlag
     AxiomatizedTypes.BranchIndex AxiomatizedTypes.Branched
     AxiomatizedTypes.BuiltInSynFamily AxiomatizedTypes.CoAxBranch
     AxiomatizedTypes.CoAxiom AxiomatizedTypes.CoAxiomRule AxiomatizedTypes.Role
     AxiomatizedTypes.Type_ AxiomatizedTypes.Unbranched BasicTypes.Arity Core.CoVar
     Core.TyCon Core.TyVar FastString.FastString GHC.Base.Eq_ GHC.Base.Ord Name.Name
     Name.NamedThing Pair.Pair SrcLoc.SrcSpan Unique.Uniquable
*)
