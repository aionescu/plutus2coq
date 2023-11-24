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
Require GHC.Num.
Require Language.Haskell.TH.Datatype.
Require Language.Haskell.TH.Lib.Internal.
Require Language.Haskell.TH.Syntax.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom mkConstrCreateExpr : BinNums.Z ->
                           list Language.Haskell.TH.Syntax.Name -> Language.Haskell.TH.Lib.Internal.ExpQ.

Axiom mkConstrPartsMatchPattern : BinNums.Z ->
                                  list Language.Haskell.TH.Syntax.Name -> Language.Haskell.TH.Lib.Internal.PatQ.

Axiom mkUnsafeConstrMatchPattern : BinNums.Z ->
                                   list Language.Haskell.TH.Syntax.Name -> Language.Haskell.TH.Lib.Internal.PatQ.

Axiom mkUnsafeConstrPartsMatchPattern : BinNums.Z ->
                                        list Language.Haskell.TH.Syntax.Name -> Language.Haskell.TH.Lib.Internal.PatQ.

Axiom toDataClause : (Language.Haskell.TH.Datatype.ConstructorInfo *
                      GHC.Num.Int)%type ->
                     Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Clause.

Axiom toDataClauses : list (Language.Haskell.TH.Datatype.ConstructorInfo *
                            GHC.Num.Int)%type ->
                      list (Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Clause).

Axiom reconstructCase : (Language.Haskell.TH.Datatype.ConstructorInfo *
                         GHC.Num.Int)%type ->
                        Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                        Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                        Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                        Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp.

Axiom fromDataClause : list (Language.Haskell.TH.Datatype.ConstructorInfo *
                             GHC.Num.Int)%type ->
                       Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Clause.

Axiom unsafeReconstructCase : (Language.Haskell.TH.Datatype.ConstructorInfo *
                               GHC.Num.Int)%type ->
                              Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                              Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                              Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp ->
                              Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp.

Axiom unsafeFromDataClause : list (Language.Haskell.TH.Datatype.ConstructorInfo
                                   *
                                   GHC.Num.Int)%type ->
                             Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Clause.

Axiom defaultIndex : Language.Haskell.TH.Syntax.Name ->
                     Language.Haskell.TH.Syntax.Q (list (Language.Haskell.TH.Syntax.Name *
                                                         GHC.Num.Int)%type).

Axiom unstableMakeIsData : Language.Haskell.TH.Syntax.Name ->
                           Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

Axiom makeIsDataIndexed : Language.Haskell.TH.Syntax.Name ->
                          list (Language.Haskell.TH.Syntax.Name * GHC.Num.Int)%type ->
                          Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

(* External variables:
     list op_zt__ BinNums.Z GHC.Num.Int Language.Haskell.TH.Datatype.ConstructorInfo
     Language.Haskell.TH.Lib.Internal.ExpQ Language.Haskell.TH.Lib.Internal.PatQ
     Language.Haskell.TH.Syntax.Clause Language.Haskell.TH.Syntax.Dec
     Language.Haskell.TH.Syntax.Exp Language.Haskell.TH.Syntax.Name
     Language.Haskell.TH.Syntax.Q
*)
